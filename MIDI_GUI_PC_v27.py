import csv
import copy
import json
import base64
import zlib
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pathlib import Path
import subprocess
import sys
import shutil
from mido import MidiFile, MidiTrack, Message, MetaMessage, bpm2tempo, tempo2bpm

TICKS_PER_BEAT = 480
BEATS_PER_BAR = 4
DEFAULT_BPM = 120
DEFAULT_BARS = 64
VISIBLE_BARS = 8
MIN_VISIBLE_BARS = 1
MAX_VISIBLE_BARS = 32

ROOTS = ['C','C#','D','Eb','E','F','F#','G','G#','A','Bb','B']
FLAT_ROOTS = ['C','Db','D','Eb','E','F','Gb','G','Ab','A','Bb','B']
ROOTS_ALL = ['C','C#','Db','D','D#','Eb','E','F','F#','Gb','G','G#','Ab','A','A#','Bb','B']
SHARP_TO_FLAT = {'C#':'Db','D#':'Eb','F#':'Gb','G#':'Ab','A#':'Bb'}
FLAT_TO_SHARP = {v:k for k,v in SHARP_TO_FLAT.items()}
NOTE_TO_PC = {'C':0,'C#':1,'Db':1,'D':2,'D#':3,'Eb':3,'E':4,'F':5,'F#':6,'Gb':6,'G':7,'G#':8,'Ab':8,'A':9,'A#':10,'Bb':10,'B':11}
DEGREE_NAMES_SHARP = ['Ⅰ','♯Ⅰ','Ⅱ','♯Ⅱ','Ⅲ','Ⅳ','♯Ⅳ','Ⅴ','♯Ⅴ','Ⅵ','♯Ⅵ','Ⅶ']
DEGREE_NAMES_FLAT = ['Ⅰ','♭Ⅱ','Ⅱ','♭Ⅲ','Ⅲ','Ⅳ','♭Ⅴ','Ⅴ','♭Ⅵ','Ⅵ','♭Ⅶ','Ⅶ']
CHORD_TYPES = ['', 'm', '7', 'maj7', 'm7', 'm7b5', 'dim', 'dim7', 'aug', 'sus4', '7sus4']
CHORDS = [r+t for t in CHORD_TYPES for r in ROOTS]
RESOLUTIONS = {'4分音符':1,'8分音符':2,'16分音符':4,'32分音符':8}
INTERVAL_NAMES = {0:'R',1:'m2',2:'M2',3:'m3',4:'M3',5:'P4',6:'A4/d5',7:'P5',8:'m6',9:'M6',10:'m7',11:'M7'}

class Bar:
    def __init__(self):
        self.key='C'
        self.accidental='sharp'
        self.split=False
        self.chord=''
        self.octave=3
        self.chord_1_2=''
        self.octave_1_2=3
        self.chord_3_4=''
        self.octave_3_4=3
        self.resolution=''  # 空欄ならTrackの分解能を継承
        self.bass=[]

def parse_note(s, allow_no_oct=True):
    s=(s or '').strip()
    if not s or s=='-':
        return None,None
    if len(s)>=2 and s[1] in '#b':
        name=s[:2]
        rest=s[2:]
    else:
        name=s[:1]
        rest=s[1:]
    name=name[0].upper()+name[1:]
    if name not in NOTE_TO_PC:
        return None,None
    if rest:
        try:
            return name,int(rest)
        except ValueError:
            return None,None
    return (name,None) if allow_no_oct else (None,None)

def midi_from_pc_oct(pc, octv):
    return (octv+1)*12+NOTE_TO_PC[pc]

def auto_midi(s, low='G2', high='F#3'):
    pc,octv=parse_note(s)
    if pc is None:
        return None
    if octv is not None:
        return midi_from_pc_oct(pc,octv)
    low_pc,low_oct=parse_note(low,allow_no_oct=False)
    high_pc,high_oct=parse_note(high,allow_no_oct=False)
    if low_pc is None or high_pc is None:
        return None
    lo=midi_from_pc_oct(low_pc,low_oct)
    hi=midi_from_pc_oct(high_pc,high_oct)
    for n in range(lo,hi+1):
        if n%12==NOTE_TO_PC[pc]:
            return n
    return None

def midi_note_name(n):
    return ROOTS[n%12]+str(n//12-1)

def normalize_note(s, low='G2', high='F#3'):
    s=(s or '').strip()
    if not s or s=='-':
        return s
    pc,octv=parse_note(s)
    if pc is None:
        return s
    if octv is not None:
        return pc+str(octv)
    n=auto_midi(s,low,high)
    return pc+str(n//12-1) if n is not None else s

def degree(note,key):
    note=(note or '').strip()
    key=(key or '').strip()
    if not note or note=='-':
        return ''
    pc,_=parse_note(note)
    key_pc,_=parse_note(key)
    if pc is None or key_pc is None:
        return ''
    interval=(NOTE_TO_PC[pc]-NOTE_TO_PC[key_pc])%12
    names=DEGREE_NAMES_FLAT if 'b' in pc else DEGREE_NAMES_SHARP
    return names[interval]

def normalize_chord_text(chord):
    chord=(chord or '').strip()
    if not chord:
        return ''
    first=chord[0]
    if first.lower() not in 'abcdefg':
        return chord
    root=first.upper()
    pos=1
    if len(chord)>1 and chord[1] in ('#','b'):
        root+=chord[1]
        pos=2
    return root+chord[pos:]

def chord_root(chord):
    chord=(chord or '').strip()
    if not chord:
        return None
    chord=normalize_chord_text(chord)
    for root in sorted(ROOTS_ALL,key=len,reverse=True):
        if chord.startswith(root):
            return root
    return None

def toggle_note_spelling(note):
    note=(note or '').strip()
    if not note or note=='-':
        return note
    pc,octv=parse_note(note)
    if pc is None:
        return note
    new_pc=SHARP_TO_FLAT.get(pc,FLAT_TO_SHARP.get(pc,pc))
    return new_pc+(str(octv) if octv is not None else '')

def toggle_chord_spelling(chord):
    chord=(chord or '').strip()
    if not chord:
        return chord
    normalized=normalize_chord_text(chord)
    root=chord_root(normalized)
    if root is None:
        return chord
    new_root=SHARP_TO_FLAT.get(root,FLAT_TO_SHARP.get(root,root))
    return new_root+normalized[len(root):]

def chord_degree(chord,key):
    chord=(chord or '').strip()
    if not chord:
        return ''
    root=chord_root(chord)
    return degree(root,key)+chord[len(root):] if root else ''

def chord_interval(note,chord):
    note=(note or '').strip()
    chord=(chord or '').strip()
    if not note:
        return ''
    if note=='-':
        return '-'
    root=chord_root(chord)
    note_pc,_=parse_note(note)
    if root is None or note_pc is None:
        return ''
    return INTERVAL_NAMES[(NOTE_TO_PC[note_pc]-NOTE_TO_PC[root])%12]

def chord_notes(chord,octv):
    chord=(chord or '').strip()
    if not chord:
        return []
    root=chord_root(chord)
    if root is None:
        return []
    suffix=chord[len(root):]
    intervals={'':[0,4,7],'m':[0,3,7],'maj7':[0,4,7,11],'m7':[0,3,7,10],'7':[0,4,7,10],'m7b5':[0,3,6,10],'dim7':[0,3,6,9],'dim':[0,3,6],'aug':[0,4,8],'sus4':[0,5,7],'7sus4':[0,5,7,10]}
    if suffix not in intervals:
        return []
    root_midi=midi_from_pc_oct(root,octv)
    return [root_midi+x for x in intervals[suffix]]

class App:
    def __init__(self,root):
        self.root=root
        self.root.bind('<Command-t>',self.shortcut_add_track)
        self.root.bind('<Control-t>',self.shortcut_add_track)
        self.root.title('Bass MIDI GUI PC v27')
        self.root.geometry('1500x900')
        self.root.minsize(1100,650)
        self.data=[Bar() for _ in range(DEFAULT_BARS)]
        self.tracks=[{'no':1,'name':'JBR_01_','bpm':DEFAULT_BPM,'resolution':'4分音符','auto_low':'G2','auto_high':'F#3','bars':self.data}]
        self.current_track=0
        self.page=0
        self.widgets=[]
        self.committers=[]
        self.bpm_var=tk.IntVar(value=DEFAULT_BPM)
        self.bars_var=tk.IntVar(value=DEFAULT_BARS)
        self.res_var=tk.StringVar(value='4分音符')
        self.auto_low_var=tk.StringVar(value='G2')
        self.auto_high_var=tk.StringVar(value='F#3')
        self.batch_key_var=tk.StringVar(value='C')
        self.batch_chord_var=tk.StringVar(value='')
        self.midi_path=None
        self.temp_work_path=Path.home()/'.bass_midi_gui_pc_work.json'
        self.player_process=None
        style=ttk.Style()
        style.configure('TButton',padding=(8,5))
        style.configure('TCombobox',padding=(1,1))
        style.configure('TEntry',padding=(1,1))
        style.configure('Bar.TLabelframe.Label',font=('',12,'bold'))
        style.configure('BarLabel.TLabel',font=('',11))
        style.configure('BarBold.TLabel',font=('',11,'bold'))
        style.configure('Bar.TCombobox',font=('',11),padding=(4,5,4,5))
        style.configure('Bar.TEntry',font=('',11),padding=(4,5,4,5))
        self.build_top()
        self.render()

    def build_top(self):
        top=ttk.Frame(self.root)
        top.pack(fill='x',padx=8,pady=6)
        ttk.Label(top,text='Track').pack(side='left')
        self.track_var=tk.StringVar(value='01')
        self.track_box=ttk.Combobox(top,textvariable=self.track_var,state='readonly',width=4)
        self.track_box.pack(side='left',padx=(3,3))
        self.track_box.bind('<<ComboboxSelected>>',self.switch_track)
        self.track_name_var=tk.StringVar(value='JBR_01_')
        ttk.Button(top,text='トラック構成',command=self.open_track_config).pack(side='left',padx=(4,3))
        ttk.Button(top,text='ファイル',command=self.open_file_menu).pack(side='left',padx=(3,10))
        self.refresh_track_box()
        ttk.Label(top,text='BPM').pack(side='left')
        ttk.Spinbox(top,from_=40,to=240,textvariable=self.bpm_var,width=5).pack(side='left',padx=(3,10))
        ttk.Label(top,text='小節数').pack(side='left')
        ttk.Spinbox(top,from_=1,to=999,textvariable=self.bars_var,width=6).pack(side='left',padx=3)
        ttk.Button(top,text='+4小節',command=lambda:self.change_bars(4)).pack(side='left',padx=3)
        ttk.Button(top,text='64小節',command=lambda:self.set_bars(64)).pack(side='left',padx=3)
        ttk.Label(top,text='ベース分解能').pack(side='left',padx=(12,3))
        res_box=ttk.Combobox(top,textvariable=self.res_var,values=list(RESOLUTIONS.keys()),state='readonly',width=10)
        res_box.pack(side='left',padx=3)
        res_box.bind('<<ComboboxSelected>>',lambda e:self.render())
        ttk.Label(top,text='表示小節数').pack(side='left',padx=(10,3))
        self.visible_bars_var=tk.IntVar(value=VISIBLE_BARS)
        visible_spin=ttk.Spinbox(top,from_=MIN_VISIBLE_BARS,to=MAX_VISIBLE_BARS,textvariable=self.visible_bars_var,width=4,command=self.change_visible_bars)
        visible_spin.pack(side='left',padx=2)
        visible_spin.bind('<Return>',lambda e:self.change_visible_bars())
        visible_spin.bind('<FocusOut>',lambda e:self.change_visible_bars())
        ttk.Label(top,text='自動音域').pack(side='left',padx=(12,3))
        ttk.Entry(top,textvariable=self.auto_low_var,width=5).pack(side='left',padx=2)
        ttk.Label(top,text='～').pack(side='left')
        ttk.Entry(top,textvariable=self.auto_high_var,width=5).pack(side='left',padx=2)
        ttk.Label(top,text='表示8小節Key一括').pack(side='left',padx=(12,3))
        key_box=ttk.Combobox(top,textvariable=self.batch_key_var,values=ROOTS,state='readonly',width=5)
        key_box.pack(side='left',padx=2)
        ttk.Button(top,text='適用',command=self.batch_key_apply).pack(side='left',padx=2)
        ttk.Label(top,text='表示4小節コード一括').pack(side='left',padx=(12,3))
        chord_box=ttk.Combobox(top,textvariable=self.batch_chord_var,values=CHORDS,width=12,state='readonly')
        chord_box.pack(side='left',padx=2)
        ttk.Button(top,text='適用',command=self.batch_chord_apply).pack(side='left',padx=2)
        nav=ttk.Frame(self.root)
        nav.pack(fill='x',padx=8,pady=(0,6))
        self.prev_button=ttk.Button(nav,text='← 前の8小節',command=lambda:self.move_page(-1))
        self.prev_button.pack(side='left',padx=3)
        self.next_button=ttk.Button(nav,text='次の8小節 →',command=lambda:self.move_page(1))
        self.next_button.pack(side='left',padx=3)
        self.page_label=ttk.Label(nav,text='')
        self.page_label.pack(side='left',padx=12)
        ttk.Label(nav,text='小節へ').pack(side='left',padx=(12,3))
        self.jump_var=tk.StringVar()
        ttk.Entry(nav,textvariable=self.jump_var,width=6).pack(side='left')
        ttk.Button(nav,text='移動',command=self.jump).pack(side='left',padx=3)

    def shortcut_add_track(self,event=None):
        self.commit_current_view()
        self.sync_track_settings()
        self.add_track()
        return 'break'

    def safe_midi_filename(self,name,index):
        name=(name or f'JBR_{index+1:02d}_').strip()
        name=re.sub(r'[\\/:*?"<>|]','_',name).rstrip('. ')
        return (name or f'JBR_{index+1:02d}_')+'.mid'

    def export_midi_tracks(self,indices):
        indices=[i for i in indices if 0<=i<len(self.tracks)]
        if not indices:return
        self.commit_current_view()
        self.sync_track_settings()
        folder=filedialog.askdirectory(title='MIDI保存先フォルダを選択')
        if not folder:return
        original=self.track_index
        try:
            for i in indices:
                self.track_index=i
                self.load_track_settings()
                path=os.path.join(folder,self.safe_midi_filename(self.tracks[i].get('name'),i))
                self.create_midi_current(path)
        finally:
            self.track_index=max(0,min(original,len(self.tracks)-1))
            self.load_track_settings()

    def open_midi_export(self):
        self.commit_current_view()
        self.sync_track_settings()
        win=tk.Toplevel(self.root)
        win.title('MIDI出力')
        win.transient(self.root)
        win.geometry('560x470')
        outer=ttk.Frame(win,padding=12)
        outer.pack(fill='both',expand=True)
        ttk.Label(outer,text='出力するExを選択',font=('',12,'bold')).pack(anchor='w',pady=(0,8))
        area=ttk.Frame(outer)
        area.pack(fill='both',expand=True)
        canvas=tk.Canvas(area,highlightthickness=0)
        scroll=ttk.Scrollbar(area,orient='vertical',command=canvas.yview)
        frame=ttk.Frame(canvas)
        frame.bind('<Configure>',lambda e:canvas.configure(scrollregion=canvas.bbox('all')))
        canvas.create_window((0,0),window=frame,anchor='nw')
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side='left',fill='both',expand=True)
        scroll.pack(side='right',fill='y')
        vars=[]
        for i,t in enumerate(self.tracks):
            v=tk.BooleanVar(value=True)
            vars.append(v)
            name=t.get('name') or f'JBR_{i+1:02d}_'
            ttk.Checkbutton(frame,text=f'Ex {i+1:02d}   {name}',variable=v).pack(anchor='w',padx=8,pady=5)
        buttons=ttk.Frame(outer)
        buttons.pack(fill='x',pady=(10,0))
        def checked():
            selected=[i for i,v in enumerate(vars) if v.get()]
            if not selected:
                messagebox.showwarning('MIDI出力','出力するExを1つ以上選択してください。',parent=win)
                return
            win.destroy()
            self.export_midi_tracks(selected)
        def all_ex():
            win.destroy()
            self.export_midi_tracks(range(len(self.tracks)))
        def current_ex():
            idx=self.track_index
            win.destroy()
            self.export_midi_tracks([idx])
        ttk.Button(buttons,text='チェックしたExを出力',command=checked).pack(side='left',padx=3)
        ttk.Button(buttons,text='全Exを出力',command=all_ex).pack(side='left',padx=3)
        ttk.Button(buttons,text='編集中Exのみ',command=current_ex).pack(side='left',padx=3)

    def open_file_menu(self):
        """ファイル関係の操作を1つの別画面に集約する。"""
        win=tk.Toplevel(self.root)
        win.title('ファイル')
        win.transient(self.root)
        win.resizable(False,False)
        body=ttk.Frame(win,padding=14)
        body.pack(fill='both',expand=True)
        ttk.Label(body,text='作業データ',font=('',12,'bold')).grid(row=0,column=0,columnspan=2,sticky='w',pady=(0,6))
        ttk.Button(body,text='一時保存',width=18,command=self.save_temp_work).grid(row=1,column=0,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='一時保存読込',width=18,command=self.load_temp_work).grid(row=1,column=1,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='プロジェクト保存',width=18,command=self.save_project).grid(row=2,column=0,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='プロジェクト読込',width=18,command=self.load_project).grid(row=2,column=1,padx=4,pady=4,sticky='ew')
        ttk.Separator(body,orient='horizontal').grid(row=3,column=0,columnspan=2,sticky='ew',pady=10)
        ttk.Label(body,text='MIDI',font=('',12,'bold')).grid(row=4,column=0,columnspan=2,sticky='w',pady=(0,6))
        ttk.Button(body,text='MIDI出力',width=18,command=self.open_midi_export).grid(row=5,column=0,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='MIDI読込',width=18,command=self.load_midi).grid(row=5,column=1,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='MIDI再生',width=18,command=self.play_midi).grid(row=6,column=0,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='停止',width=18,command=self.stop_midi).grid(row=6,column=1,padx=4,pady=4,sticky='ew')
        ttk.Separator(body,orient='horizontal').grid(row=7,column=0,columnspan=2,sticky='ew',pady=10)
        ttk.Label(body,text='CSV',font=('',12,'bold')).grid(row=8,column=0,columnspan=2,sticky='w',pady=(0,6))
        ttk.Button(body,text='CSV保存',width=18,command=self.save_csv).grid(row=9,column=0,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='CSV読込',width=18,command=self.load_csv).grid(row=9,column=1,padx=4,pady=4,sticky='ew')
        ttk.Button(body,text='閉じる',command=win.destroy).grid(row=10,column=0,columnspan=2,pady=(12,0))
        win.grab_set()
        win.focus_set()

    def track_input_bar_count(self,t):
        """入力がある小節数を数える。途中の空白小節は数えない。"""
        count=0
        for b in t.get('bars',[]):
            has_chord=bool((b.chord or '').strip() or (b.chord_1_2 or '').strip() or (b.chord_3_4 or '').strip())
            has_bass=any(str(x).strip() and str(x).strip()!='-' for x in b.bass)
            if has_chord or has_bass:
                count+=1
        return count

    def open_track_config(self):
        """Track名編集・入力済小節数・8Track単位ページ・削除/元に戻す。"""
        self.commit_current_view()
        self.sync_track_settings()
        win=tk.Toplevel(self.root)
        win.title('トラック構成')
        win.transient(self.root)
        win.geometry('650x430')
        win.resizable(False,False)
        outer=ttk.Frame(win,padding=12)
        outer.pack(fill='both',expand=True)
        page_size=8
        state={'page':0,'undo':None}
        name_vars={}

        header=ttk.Frame(outer)
        header.pack(fill='x')
        ttk.Label(header,text='Ex',width=8,anchor='center',font=('',11,'bold')).grid(row=0,column=0,padx=4,pady=5)
        ttk.Label(header,text='トラック名',width=30,anchor='w',font=('',11,'bold')).grid(row=0,column=1,padx=4,pady=5)
        ttk.Label(header,text='入力済小節数',width=12,anchor='center',font=('',11,'bold')).grid(row=0,column=2,padx=4,pady=5)
        ttk.Label(header,text='',width=8).grid(row=0,column=3,padx=4,pady=5)

        rows=ttk.Frame(outer)
        rows.pack(fill='both',expand=True)

        nav=ttk.Frame(outer)
        nav.pack(fill='x',pady=(8,0))
        page_var=tk.StringVar()
        undo_btn=None

        def save_visible_names():
            for i,v in list(name_vars.items()):
                if 0<=i<len(self.tracks):
                    no=int(self.tracks[i].get('no',i+1))
                    self.tracks[i]['name']=v.get().strip() or f'JBR_{no:02d}_'
            if 0<=self.track_index<len(self.tracks):
                self.load_track_settings()

        def renumber_tracks():
            for i,t in enumerate(self.tracks):
                t['no']=i+1
                if not (t.get('name') or '').strip():
                    t['name']=f'JBR_{i+1:02d}_'

        def rebuild():
            nonlocal undo_btn
            for child in rows.winfo_children():
                child.destroy()
            name_vars.clear()
            max_page=max(0,(len(self.tracks)-1)//page_size)
            state['page']=max(0,min(state['page'],max_page))
            first=state['page']*page_size
            last=min(first+page_size,len(self.tracks))
            for r,i in enumerate(range(first,last)):
                t=self.tracks[i]
                ttk.Label(rows,text=f"Ex {i+1:02d}",width=8,anchor='center').grid(row=r,column=0,padx=4,pady=6)
                v=tk.StringVar(value=t.get('name') or f"JBR_{i+1:02d}_")
                name_vars[i]=v
                e=ttk.Entry(rows,textvariable=v,width=30)
                e.grid(row=r,column=1,padx=4,pady=6,sticky='ew')
                ttk.Label(rows,text=str(self.track_input_bar_count(t)),width=12,anchor='center').grid(row=r,column=2,padx=4,pady=6)
                ttk.Button(rows,text='削除',width=7,command=lambda idx=i:delete_track(idx)).grid(row=r,column=3,padx=4,pady=6)
            rows.columnconfigure(1,weight=1)
            page_var.set(f'{state["page"]+1} / {max_page+1}')
            if undo_btn is not None:
                undo_btn.configure(state='normal' if state['undo'] is not None else 'disabled')

        def prev_page():
            save_visible_names()
            if state['page']>0:
                state['page']-=1
                rebuild()

        def next_page():
            save_visible_names()
            if (state['page']+1)*page_size<len(self.tracks):
                state['page']+=1
                rebuild()

        def add_from_config():
            save_visible_names()
            self.add_track()
            state['page']=(len(self.tracks)-1)//page_size
            rebuild()

        def delete_track(idx):
            save_visible_names()
            if len(self.tracks)<=1:
                messagebox.showwarning('削除できません','Trackは最低1つ必要です。',parent=win)
                return
            t=self.tracks[idx]
            label=t.get('name') or f'Track {idx+1:02d}'
            if not messagebox.askokcancel('Track削除',f'Ex {idx+1:02d}「{label}」を削除します。',parent=win):
                return
            state['undo']=(idx,t,self.track_index)
            del self.tracks[idx]
            renumber_tracks()
            if self.track_index==idx:
                self.track_index=min(idx,len(self.tracks)-1)
            elif self.track_index>idx:
                self.track_index-=1
            self.load_track_settings()
            rebuild()

        def undo_delete():
            if state['undo'] is None:
                return
            idx,t,old_current=state['undo']
            idx=max(0,min(idx,len(self.tracks)))
            self.tracks.insert(idx,t)
            renumber_tracks()
            self.track_index=max(0,min(old_current,len(self.tracks)-1))
            state['undo']=None
            self.load_track_settings()
            state['page']=idx//page_size
            rebuild()

        ttk.Button(nav,text='◀',width=5,command=prev_page).pack(side='left',padx=4)
        ttk.Label(nav,textvariable=page_var,width=9,anchor='center').pack(side='left')
        ttk.Button(nav,text='▶',width=5,command=next_page).pack(side='left',padx=4)
        ttk.Button(nav,text='+ トラック追加',command=add_from_config).pack(side='left',padx=(14,4))
        undo_btn=ttk.Button(nav,text='元に戻す',command=undo_delete)
        undo_btn.pack(side='left',padx=4)
        ttk.Button(nav,text='閉じる',command=lambda:(save_visible_names(),win.destroy())).pack(side='right',padx=4)
        rebuild()
        win.protocol('WM_DELETE_WINDOW',lambda:(save_visible_names(),win.destroy()))
        win.focus_set()

    def refresh_track_box(self):
        if not hasattr(self,'track_box'):
            return
        vals=[f"{int(t.get('no',i+1)):02d}" for i,t in enumerate(self.tracks)]
        self.track_box['values']=vals
        if vals:
            self.track_var.set(vals[self.current_track])

    def sync_track_settings(self):
        if not self.tracks:
            return
        t=self.tracks[self.current_track]
        t['name']=self.track_name_var.get().strip() or f"Track {int(t.get('no',self.current_track+1)):02d}"
        t['bpm']=int(self.bpm_var.get())
        t['resolution']=self.res_var.get()
        t['auto_low']=self.auto_low_var.get()
        t['auto_high']=self.auto_high_var.get()
        t['bars']=self.data

    def load_track_settings(self):
        t=self.tracks[self.current_track]
        self.data=t['bars']
        self.bars_var.set(len(self.data))
        self.track_name_var.set(t.get('name',f"Track {self.current_track+1:02d}"))
        self.bpm_var.set(int(t.get('bpm',DEFAULT_BPM)))
        self.res_var.set(t.get('resolution','4分音符'))
        self.auto_low_var.set(t.get('auto_low','G2'))
        self.auto_high_var.set(t.get('auto_high','F#3'))
        self.refresh_track_box()

    def switch_track(self,event=None):
        self.commit_current_view()
        self.sync_track_settings()
        try:
            idx=list(self.track_box['values']).index(self.track_var.get())
        except ValueError:
            return
        self.current_track=idx
        self.page=0
        self.load_track_settings()
        self.render()

    def add_track(self):
        self.commit_current_view(); self.sync_track_settings()
        no=max([int(t.get('no',0)) for t in self.tracks]+[0])+1
        bars=[Bar() for _ in range(DEFAULT_BARS)]
        self.tracks.append({'no':no,'name':f'JBR_{no:02d}_','bpm':DEFAULT_BPM,'resolution':'4分音符','auto_low':'G2','auto_high':'F#3','bars':bars})
        self.current_track=len(self.tracks)-1
        self.page=0
        self.load_track_settings()
        self.render()

    def get_visible_bars(self):
        try:
            return max(MIN_VISIBLE_BARS,min(MAX_VISIBLE_BARS,int(self.visible_bars_var.get())))
        except (ValueError,tk.TclError):
            return VISIBLE_BARS

    def change_visible_bars(self):
        n=self.get_visible_bars()
        self.visible_bars_var.set(n)
        self.page=min(self.page,max(0,(len(self.data)-1)//n))
        self.prev_button.config(text=f'← 前の{n}小節')
        self.next_button.config(text=f'次の{n}小節 →')
        self.render()

    def set_bars(self,n):
        n=max(1,int(n))
        if n>len(self.data):
            self.data.extend(Bar() for _ in range(n-len(self.data)))
        else:
            self.data=self.data[:n]
        self.bars_var.set(n)
        self.page=min(self.page,max(0,(len(self.data)-1)//self.get_visible_bars()))
        self.render()

    def change_bars(self,delta):
        self.set_bars(len(self.data)+delta)

    def move_page(self,delta):
        max_page=max(0,(len(self.data)-1)//self.get_visible_bars())
        self.page=max(0,min(max_page,self.page+delta))
        self.render()

    def jump(self):
        try:
            bar_no=int(self.jump_var.get())
        except ValueError:
            return
        if 1<=bar_no<=len(self.data):
            self.page=(bar_no-1)//self.get_visible_bars()
            self.render()

    def batch_key_apply(self):
        key=self.batch_key_var.get()
        if not key:
            return
        visible=self.get_visible_bars()
        start=self.page*visible
        end=min(start+visible,len(self.data))
        for i in range(start,end):
            self.data[i].key=key
        self.render()

    def batch_chord_apply(self):
        chord=self.batch_chord_var.get().strip()
        visible=self.get_visible_bars()
        start=self.page*visible
        end=min(start+4,len(self.data))
        for i in range(start,end):
            self.data[i].split=False
            self.data[i].chord=chord
        self.render()

    def commit_current_view(self):
        for commit in getattr(self,'committers',[]):
            commit()

    def copy_previous_bar(self,bar_index):
        if bar_index<=0:
            return
        self.sync_visible_data()
        src=self.data[bar_index-1]
        dst=self.data[bar_index]
        dst.key=src.key
        dst.split=src.split
        dst.chord=src.chord
        dst.octave=src.octave
        dst.chord_1_2=src.chord_1_2
        dst.octave_1_2=src.octave_1_2
        dst.chord_3_4=src.chord_3_4
        dst.octave_3_4=src.octave_3_4
        dst.resolution=src.resolution
        dst.bass=list(src.bass)
        self.render()

    def toggle_bar_accidental(self,bar_index):
        """小節内のKey/Chord/Bassを #系/♭系で一括切替。"""
        if not (0 <= bar_index < len(self.data)):
            return
        b=self.data[bar_index]
        mode='flat' if getattr(b,'accidental','sharp')=='sharp' else 'sharp'
        b.accidental=mode
        sf={'C#':'Db','D#':'Eb','F#':'Gb','G#':'Ab','A#':'Bb'}
        table=sf if mode=='flat' else {v:k for k,v in sf.items()}
        def cv(text):
            if not text:return text
            for a,z in table.items():
                text=text.replace(a,z)
            return text
        b.key=cv(b.key)
        b.chord=cv(b.chord)
        b.chord_1_2=cv(b.chord_1_2)
        b.chord_3_4=cv(b.chord_3_4)
        b.bass=[cv(x) for x in b.bass]
        self.render()

    def render(self):
        self.commit_current_view()
        self.committers=[]
        self.input_focus_widgets=[]
        for w in self.widgets:
            w.destroy()
        self.widgets=[]
        visible=self.get_visible_bars()
        start=self.page*visible
        end=min(start+visible,len(self.data))
        self.page_label.config(text=f'{start+1}～{end}小節 / 全{len(self.data)}小節')
        container=ttk.Frame(self.root)
        container.pack(fill='both',expand=True,padx=8,pady=4)
        self.widgets.append(container)
        legend=ttk.Frame(container)
        legend.grid(row=0,column=0,columnspan=4,sticky='w',padx=4,pady=(0,5))
        tk.Label(legend,text='● Keyから見た度数',fg='green',font=('',14,'bold')).pack(side='left',padx=(0,18))
        tk.Label(legend,text='● コードルートから見た度数',fg='purple',font=('',14,'bold')).pack(side='left')
        for c in range(4):
            container.columnconfigure(c,weight=1)
        for pos,i in enumerate(range(start,end)):
            row=pos//4+1
            col=pos%4
            self.build_bar(container,i,self.data[i],row,col)
        self.bind_serial_tab_navigation()

    def bind_serial_tab_navigation(self):
        for widget in self.input_focus_widgets:
            widget.bind('<Tab>',lambda e,w=widget:self.move_input_focus(w,1))
            widget.bind('<Shift-Tab>',lambda e,w=widget:self.move_input_focus(w,-1))

    def move_input_focus(self,widget,direction):
        if not self.input_focus_widgets:
            return 'break'
        try:
            i=self.input_focus_widgets.index(widget)
        except ValueError:
            return 'break'
        j=i+direction
        if 0<=j<len(self.input_focus_widgets):
            self.input_focus_widgets[j].focus_set()
            return 'break'
        visible=self.get_visible_bars()
        max_page=max(0,(len(self.data)-1)//visible)
        if direction>0 and self.page<max_page:
            self.commit_current_view()
            self.page+=1
            self.render()
            if self.input_focus_widgets:
                self.root.after_idle(self.input_focus_widgets[0].focus_set)
        elif direction<0 and self.page>0:
            self.commit_current_view()
            self.page-=1
            self.render()
            if self.input_focus_widgets:
                self.root.after_idle(self.input_focus_widgets[-1].focus_set)
        return 'break'

    def normalize_entry(self,var):
        raw=var.get().strip()
        if not raw or raw=='-':
            return
        normalized=normalize_note(raw,self.auto_low_var.get(),self.auto_high_var.get())
        var.set(normalized)

    def toggle_note_var(self,var):
        raw=var.get().strip()
        if not raw or raw=='-':
            return
        normalized=normalize_note(raw,self.auto_low_var.get(),self.auto_high_var.get())
        var.set(toggle_note_spelling(normalized))

    def normalize_chord_var(self,var):
        raw=var.get()
        normalized=normalize_chord_text(raw)
        if normalized!=raw:
            var.set(normalized)

    def toggle_chord_var(self,var):
        self.normalize_chord_var(var)
        var.set(toggle_chord_spelling(var.get()))

    def build_bar(self,parent,index,b,row,col):
        frame=ttk.LabelFrame(parent,text=f'小節 {index+1}',style='Bar.TLabelframe')
        frame.grid(row=row,column=col,sticky='nsew',padx=2,pady=2)
        key=tk.StringVar(value=b.key)
        split=tk.BooleanVar(value=b.split)
        chord=tk.StringVar(value=b.chord)
        c12=tk.StringVar(value=b.chord_1_2)
        c34=tk.StringVar(value=b.chord_3_4)
        chord_oct=tk.IntVar(value=b.octave)
        oct12=tk.IntVar(value=b.octave_1_2)
        oct34=tk.IntVar(value=b.octave_3_4)
        bar_res=tk.StringVar(value=b.resolution or 'Track')

        key_row=ttk.Frame(frame)
        key_row.grid(row=0,column=0,sticky='w',padx=4,pady=(2,1))
        ttk.Label(key_row,text='Key',style='BarLabel.TLabel').pack(side='left')
        key_box=ttk.Combobox(key_row,textvariable=key,values=ROOTS,state='readonly',width=4,takefocus=False,style='Bar.TCombobox')
        key_box.pack(side='left',padx=(2,4))
        ttk.Button(key_row,text='#/♭',width=5,command=lambda idx=index:self.toggle_bar_accidental(idx)).pack(side='left',padx=(1,4))
        ttk.Label(key_row,text='分解能',style='BarLabel.TLabel').pack(side='left',padx=(3,1))
        bar_res_box=ttk.Combobox(key_row,textvariable=bar_res,values=['Track']+list(RESOLUTIONS.keys()),state='readonly',width=8,takefocus=False)
        bar_res_box.pack(side='left',padx=(1,4))

        chord_row=ttk.Frame(frame)
        chord_row.grid(row=1,column=0,sticky='w',padx=4,pady=1)
        ttk.Label(chord_row,text='Chord',style='BarLabel.TLabel').pack(side='left')

        def make_chord_input(parent_row,label,var,oct_var):
            ttk.Label(parent_row,text=label,style='BarLabel.TLabel').pack(side='left',padx=(3,1))
            box=ttk.Combobox(parent_row,textvariable=var,values=CHORDS,width=9,height=18,takefocus=True,style='Bar.TCombobox',state='readonly')
            box.pack(side='left',padx=(0,2),pady=2)
            box.bind('<KeyRelease>',lambda e,v=var:self.normalize_chord_var(v))
            box.bind('<Return>',lambda e,v=var:self.normalize_chord_var(v))
            box.bind('<FocusOut>',lambda e,v=var:self.normalize_chord_var(v))
            box.bind('<<ComboboxSelected>>',lambda e,v=var:self.normalize_chord_var(v))
            ttk.Spinbox(parent_row,from_=0,to=8,textvariable=oct_var,width=3,takefocus=False).pack(side='left',padx=(0,2))
            self.input_focus_widgets.append(box)
            # ComboBox本体を大きくし、隣接する空き部分からもフォーカスしやすくする。
            box.bind('<Button-1>',lambda e,w=box:w.focus_set(),add='+')
            return box

        if not b.split:
            make_chord_input(chord_row,'',chord,chord_oct)
            chord_degree_label=ttk.Label(chord_row,text='',foreground='blue',width=9,font=('',16,'bold'))
            chord_degree_label.pack(side='left',padx=3)
        else:
            make_chord_input(chord_row,'1-2拍',c12,oct12)
            make_chord_input(chord_row,'3-4拍',c34,oct34)
            chord_degree_label=ttk.Label(chord_row,text='',foreground='blue',width=11,font=('',16,'bold'))
            chord_degree_label.pack(side='left',padx=3)

        ttk.Checkbutton(key_row,text='2拍分割',variable=split,takefocus=False).pack(side='left',padx=3)

        bass_row=ttk.Frame(frame)
        bass_row.grid(row=2,column=0,sticky='w',padx=4,pady=(3,5))
        ttk.Label(bass_row,text='Bass',font=('',11,'bold')).grid(row=0,column=0,padx=(0,3),sticky='nw')
        effective_res=b.resolution if b.resolution in RESOLUTIONS else self.res_var.get()
        sub=RESOLUTIONS[effective_res]
        count=sub*BEATS_PER_BAR
        while len(b.bass)<count:
            b.bass.append('')
        bass=[]
        bass_key_labels=[]
        bass_chord_labels=[]

        for i in range(count):
            cell=ttk.Frame(bass_row)
            cell.grid(row=0,column=i+1,padx=1,pady=0,sticky='n')
            sv=tk.StringVar(value=b.bass[i])
            beat=i//sub+1
            subdivision=i%sub+1
            pos_text=str(beat) if sub==1 else f'{beat}.{subdivision}'
            pos_label=ttk.Label(cell,text=pos_text,font=('',10))
            pos_label.pack(pady=(0,1))
            entry=ttk.Entry(cell,textvariable=sv,width=5,justify='center',takefocus=True,style='Bar.TEntry')
            entry.pack(pady=(1,2))
            dg_key=ttk.Label(cell,text='',foreground='green',width=5,anchor='center',font=('',16,'bold'))
            dg_key.pack()
            dg_chord=ttk.Label(cell,text='',foreground='purple',width=6,anchor='center',font=('',16,'bold'))
            dg_chord.pack()
            # 入力欄周辺もクリック領域として使う。
            focus_bass=lambda e,w=entry:w.focus_set()
            cell.bind('<Button-1>',focus_bass)
            pos_label.bind('<Button-1>',focus_bass)
            dg_key.bind('<Button-1>',focus_bass)
            dg_chord.bind('<Button-1>',focus_bass)
            self.input_focus_widgets.append(entry)
            entry.bind('<Return>',lambda e,v=sv:self.normalize_entry(v))
            entry.bind('<FocusOut>',lambda e,v=sv:self.normalize_entry(v))
            bass.append(sv)
            bass_key_labels.append(dg_key)
            bass_chord_labels.append(dg_chord)

        def current_chord(i):
            if not split.get():
                return chord.get()
            current_sub=sub
            return c12.get() if i<2*current_sub else c34.get()

        def refresh_bass_degrees():
            for i,sv in enumerate(bass):
                raw=sv.get().strip()
                bass_key_labels[i].config(text=degree(raw,key.get()))
                bass_chord_labels[i].config(text=chord_interval(raw,current_chord(i)))

        def refresh_chord_degree(*args):
            if not split.get():
                text=chord_degree(chord.get(),key.get())
            else:
                text=f'{chord_degree(c12.get(),key.get())} / {chord_degree(c34.get(),key.get())}'
            chord_degree_label.config(text=text)
            refresh_bass_degrees()

        for var in (chord,c12,c34,key):
            var.trace_add('write',refresh_chord_degree)
        for sv in bass:
            sv.trace_add('write',lambda *args:refresh_bass_degrees())

        def apply_bar_controls():
            b.key=key.get()
            b.split=split.get()
            b.chord=chord.get().strip()
            b.octave=chord_oct.get()
            b.chord_1_2=c12.get().strip()
            b.octave_1_2=oct12.get()
            b.chord_3_4=c34.get().strip()
            b.octave_3_4=oct34.get()
            b.resolution='' if bar_res.get()=='Track' else bar_res.get()
            b.bass=[sv.get().strip() for sv in bass]

        self.committers.append(apply_bar_controls)

        def key_changed(event=None):
            b.key=key.get()
            refresh_chord_degree()

        def split_changed():
            apply_bar_controls()
            self.render()

        key_box.bind('<<ComboboxSelected>>',key_changed)
        def bar_resolution_changed(event=None):
            apply_bar_controls(); self.render()
        bar_res_box.bind('<<ComboboxSelected>>',bar_resolution_changed)
        for child in key_row.winfo_children():
            if isinstance(child,ttk.Checkbutton):
                child.configure(command=split_changed)

        refresh_chord_degree()

    def bar_to_dict(self,b):
        return {'key':b.key,'accidental':getattr(b,'accidental','sharp'),'split':b.split,'chord':b.chord,'octave':b.octave,
            'chord_1_2':b.chord_1_2,'octave_1_2':b.octave_1_2,'chord_3_4':b.chord_3_4,
            'octave_3_4':b.octave_3_4,'resolution':b.resolution,'bass':list(b.bass)}

    def dict_to_bar(self,item):
        b=Bar(); b.key=item.get('key','C')
        b.accidental=item.get('accidental','sharp') or 'sharp'; b.split=bool(item.get('split',False)); b.chord=item.get('chord','')
        b.octave=int(item.get('octave',3)); b.chord_1_2=item.get('chord_1_2',''); b.octave_1_2=int(item.get('octave_1_2',3))
        b.chord_3_4=item.get('chord_3_4',''); b.octave_3_4=int(item.get('octave_3_4',3)); b.resolution=item.get('resolution','') or ''
        bass=item.get('bass',[])
        b.bass=['' if x is None else str(x) for x in bass] if isinstance(bass,list) else []
        return b

    def state_dict(self):
        self.commit_current_view(); self.sync_track_settings()
        tracks=[]
        for t in self.tracks:
            tracks.append({'no':t['no'],'name':t['name'],'bpm':t['bpm'],'resolution':t['resolution'],
                'auto_low':t.get('auto_low','G2'),'auto_high':t.get('auto_high','F#3'),'bars':[self.bar_to_dict(b) for b in t['bars']]})
        return {'format':'bass-midi-gui-multitrack','format_version':3,'app':'Bass MIDI GUI PC','version':'26',
            'project_name':'bass_project','visible_bars':self.get_visible_bars(),'tracks':tracks}

    def apply_state_dict(self,state):
        # v24/iPhone v11 multitrack, plus legacy PC single-track JSON.
        if state.get('format')=='bass-midi-gui-multitrack' or state.get('tracks'):
            src_tracks=state.get('tracks',[])
        else:
            src_tracks=[{'no':1,'name':'JBR_01_','bpm':state.get('bpm',DEFAULT_BPM),'resolution':state.get('resolution','4分音符'),
                'auto_low':state.get('auto_low','G2'),'auto_high':state.get('auto_high','F#3'),'bars':state.get('bars',[])}]
        if not src_tracks: raise ValueError('Track情報がありません。')
        tracks=[]
        for i,t in enumerate(src_tracks):
            raw_bars=t.get('bars',[])
            if not isinstance(raw_bars,list):
                raw_bars=[]
            bars=[self.dict_to_bar(x) for x in raw_bars if isinstance(x,dict)] or [Bar()]
            tracks.append({'no':int(t.get('no',i+1)),'name':t.get('name') or f'JBR_{i+1:02d}_','bpm':int(round(float(t.get('bpm',DEFAULT_BPM)))),
                'resolution':t.get('resolution','4分音符') if t.get('resolution') in RESOLUTIONS else '4分音符',
                'auto_low':t.get('auto_low','G2'),'auto_high':t.get('auto_high','F#3'),'bars':bars})
        self.tracks=tracks; self.current_track=0
        if state.get('visible_bars') is not None:self.visible_bars_var.set(max(MIN_VISIBLE_BARS,min(MAX_VISIBLE_BARS,int(state['visible_bars']))))
        self.page=0; self.load_track_settings(); self.change_visible_bars()

    def save_project(self):
        try:
            state=self.state_dict()
            path=filedialog.asksaveasfilename(
                defaultextension='.json',
                filetypes=[('Bass MIDI GUI Project (JSON)','*.json'),('旧Bass Project','*.bassproj'),('Text','*.txt'),('すべてのファイル','*.*')]
            )
            if not path:
                return
            Path(path).write_text(json.dumps(state,ensure_ascii=False,indent=2),encoding='utf-8')
            messagebox.showinfo('プロジェクト保存','複数Track対応のPC/iPhone共通プロジェクトを保存しました。')
        except Exception as e:
            messagebox.showerror('プロジェクト保存エラー',str(e))

    def load_project(self):
        path=filedialog.askopenfilename(
            filetypes=[('Bass MIDI GUI Project','*.json *.bassproj *.txt'),('JSON','*.json'),('旧Bass Project','*.bassproj'),('Text','*.txt'),('すべてのファイル','*.*')]
        )
        if not path:
            return
        try:
            state=json.loads(Path(path).read_text(encoding='utf-8'))
            if not isinstance(state,dict):
                raise ValueError('JSONの最上位がオブジェクトではありません。')
            if state.get('format') not in (None,'bassproj','bass-midi-gui-project','bass-midi-gui-multitrack'):
                raise ValueError('Bass MIDI GUIのプロジェクト形式ではありません。')
            self.apply_state_dict(state)
            # macOS + Python.org 3.10/Tk 8.6 では、読込直後のNSAlert(messagebox)が
            # AppKit側でSIGABRTする場合があるため、成功時はモーダルダイアログを出さない。
            self.root.title(f'Bass MIDI GUI PC v27 - {Path(path).name}')
            print(f'プロジェクト読込完了: {path}')
        except Exception as e:
            # エラー時もNSAlertを避け、Python自体が落ちないようにする。
            print(f'プロジェクト読込エラー: {type(e).__name__}: {e}')
            self.root.title(f'Bass MIDI GUI PC v27 - 読込エラー')

    def save_temp_work(self):
        try:
            state=self.state_dict()
            self.temp_work_path.write_text(json.dumps(state,ensure_ascii=False,indent=2),encoding='utf-8')
            messagebox.showinfo('一時保存',f'現在の作業内容を一時保存しました。\n{self.temp_work_path}')
        except Exception as e:
            messagebox.showerror('一時保存エラー',str(e))

    def load_temp_work(self):
        if not self.temp_work_path.exists():
            messagebox.showwarning('一時復元','一時保存された作業データがありません。')
            return
        try:
            state=json.loads(self.temp_work_path.read_text(encoding='utf-8'))
            self.apply_state_dict(state)
            messagebox.showinfo('一時復元','一時保存した作業内容を復元しました。')
        except Exception as e:
            messagebox.showerror('一時復元エラー',str(e))

    def encode_state_chunks(self):
        raw=json.dumps(self.state_dict(),ensure_ascii=False,separators=(',',':')).encode('utf-8')
        encoded=base64.b64encode(zlib.compress(raw,9)).decode('ascii')
        size=180
        parts=[encoded[i:i+size] for i in range(0,len(encoded),size)]
        total=len(parts)
        return [f'BMGSTATE:{i+1:04d}/{total:04d}:{part}' for i,part in enumerate(parts)]

    def decode_state_from_midi(self,mid):
        parts={}
        total=None
        for track in mid.tracks:
            for msg in track:
                if msg.type=='text' and getattr(msg,'text','').startswith('BMGSTATE:'):
                    text=msg.text
                    try:
                        head,payload=text.split(':',2)[1:]
                        no,total_text=head.split('/')
                        parts[int(no)]=payload
                        total=int(total_text)
                    except Exception:
                        continue
        if not parts or total is None or len(parts)!=total:
            return None
        encoded=''.join(parts[i] for i in range(1,total+1))
        raw=zlib.decompress(base64.b64decode(encoded)).decode('utf-8')
        return json.loads(raw)

    def chord_name_from_notes(self,notes):
        if not notes:
            return '',3
        root=min(notes)
        root_pc=root%12
        rel=tuple(sorted({(n-root)%12 for n in notes}))
        patterns={
            (0,4,7):'',(0,3,7):'m',(0,4,7,10):'7',(0,4,7,11):'maj7',
            (0,3,7,10):'m7',(0,3,6,10):'m7b5',(0,3,6):'dim',(0,3,6,9):'dim7',
            (0,4,8):'aug',(0,5,7):'sus4',(0,5,7,10):'7sus4'
        }
        suffix=patterns.get(rel,'')
        return ROOTS[root_pc]+suffix,root//12-1

    def reconstruct_state_from_midi(self,mid):
        tpb=mid.ticks_per_beat
        tempo=500000
        for track in mid.tracks:
            for msg in track:
                if msg.type=='set_tempo':
                    tempo=msg.tempo
                    break
        # Bass note positions and shortest step determine resolution.
        bass_events=[]
        chord_starts={}
        for track in mid.tracks:
            name=''
            abs_t=0
            active={}
            groups={}
            for msg in track:
                abs_t+=msg.time
                if msg.type=='track_name':
                    name=msg.name
                elif msg.type=='note_on' and msg.velocity>0:
                    active.setdefault((msg.channel,msg.note),[]).append(abs_t)
                    if name=='Chords':
                        groups.setdefault(abs_t,[]).append(msg.note)
                elif msg.type in ('note_off','note_on') and (msg.type=='note_off' or msg.velocity==0):
                    starts=active.get((getattr(msg,'channel',0),msg.note),[])
                    if starts:
                        st=starts.pop(0)
                        if name=='Bass' and msg.note!=0:
                            bass_events.append((st,msg.note,max(1,abs_t-st)))
            if name=='Chords':
                chord_starts.update(groups)
        durations=[d for _,_,d in bass_events]
        if durations:
            step=min(durations)
            sub=max(1,min(8,round(tpb/step)))
        else:
            sub=1
        res={1:'4分音符',2:'8分音符',4:'16分音符',8:'32分音符'}.get(sub,'4分音符')
        bar_ticks=tpb*4
        max_tick=0
        if bass_events:
            max_tick=max(max_tick,max(st+d for st,_,d in bass_events))
        if chord_starts:
            max_tick=max(max_tick,max(chord_starts.keys())+bar_ticks)
        bar_count=max(1,(max_tick+bar_ticks-1)//bar_ticks)
        bars=[Bar() for _ in range(bar_count)]
        for st,n,_ in bass_events:
            bar_i=st//bar_ticks
            within=st%bar_ticks
            pos=round(within/(tpb/sub))
            if 0<=bar_i<len(bars) and 0<=pos<sub*4:
                while len(bars[bar_i].bass)<sub*4:
                    bars[bar_i].bass.append('')
                bars[bar_i].bass[pos]=midi_note_name(n)
        for st,notes in sorted(chord_starts.items()):
            bar_i=st//bar_ticks
            within=st%bar_ticks
            if not (0<=bar_i<len(bars)):
                continue
            chord,octv=self.chord_name_from_notes(notes)
            if within<tpb:
                bars[bar_i].chord=chord
                bars[bar_i].octave=octv
            elif abs(within-2*tpb)<=tpb//4:
                if bars[bar_i].chord:
                    bars[bar_i].split=True
                    bars[bar_i].chord_1_2=bars[bar_i].chord
                    bars[bar_i].octave_1_2=bars[bar_i].octave
                    bars[bar_i].chord=''
                bars[bar_i].chord_3_4=chord
                bars[bar_i].octave_3_4=octv
        return {
            'app':'Bass MIDI GUI PC','version':'reconstructed',
            'bpm':round(tempo2bpm(tempo)),'resolution':res,
            'auto_low':self.auto_low_var.get(),'auto_high':self.auto_high_var.get(),
            'visible_bars':self.get_visible_bars(),
            'bars':[{
                'key':b.key,'accidental':getattr(b,'accidental','sharp'),'split':b.split,'chord':b.chord,'octave':b.octave,
                'chord_1_2':b.chord_1_2,'octave_1_2':b.octave_1_2,
                'chord_3_4':b.chord_3_4,'octave_3_4':b.octave_3_4,'bass':b.bass
            } for b in bars]
        }

    def load_midi(self):
        path=filedialog.askopenfilename(filetypes=[('MIDI','*.mid *.midi'),('すべてのファイル','*.*')])
        if not path:
            return
        try:
            mid=MidiFile(path)
            state=self.decode_state_from_midi(mid)
            exact=state is not None
            if state is None:
                state=self.reconstruct_state_from_midi(mid)
            self.apply_state_dict(state)
            self.midi_path=path
            if exact:
                messagebox.showinfo('MIDI読込','このアプリで保存された編集情報を含むMIDIを読み込み、作業状態を復元しました。')
            else:
                messagebox.showinfo('MIDI読込','MIDI音符から編集状態を可能な範囲で復元しました。\nKeyや異名同音表記など、MIDIに含まれない情報は完全には復元できません。')
        except Exception as e:
            messagebox.showerror('MIDI読込エラー',str(e))

    def last_bar(self):
        last=-1
        for i,b in enumerate(self.data):
            has_chord=bool(b.chord.strip() or b.chord_1_2.strip() or b.chord_3_4.strip())
            has_bass=any(x.strip() and x.strip()!='-' for x in b.bass)
            if has_chord or has_bass:
                last=i
        return last

    def save_csv(self):
        self.commit_current_view()
        path=filedialog.asksaveasfilename(defaultextension='.csv',filetypes=[('CSV','*.csv')])
        if not path:
            return
        rows=[]
        for i,b in enumerate(self.data):
            rows.append([i+1,b.key,int(b.split),b.chord,b.octave,b.chord_1_2,b.octave_1_2,b.chord_3_4,b.octave_3_4,b.resolution]+b.bass)
        with open(path,'w',newline='',encoding='utf-8-sig') as f:
            csv.writer(f).writerows(rows)
        messagebox.showinfo('CSV保存','CSVを保存しました。')

    def load_csv(self):
        path=filedialog.askopenfilename(filetypes=[('CSV','*.csv')])
        if not path:
            return
        try:
            with open(path,'r',newline='',encoding='utf-8-sig') as f:
                rows=list(csv.reader(f))
            self.data=[]
            for row in rows:
                if len(row)<9:
                    continue
                b=Bar()
                b.key=row[1] or 'C'
                try:
                    b.split=bool(int(row[2]))
                except ValueError:
                    b.split=False
                b.chord=row[3]
                b.octave=int(row[4] or 3)
                b.chord_1_2=row[5]
                b.octave_1_2=int(row[6] or 3)
                b.chord_3_4=row[7]
                b.octave_3_4=int(row[8] or 3)
                if len(row)>9 and row[9] in ('',*RESOLUTIONS.keys()):
                    b.resolution=row[9]; b.bass=row[10:]
                else:
                    b.bass=row[9:]
                self.data.append(b)
            if not self.data:
                self.data=[Bar()]
            self.bars_var.set(len(self.data))
            self.page=0
            self.render()
            messagebox.showinfo('CSV読込','CSVを読み込みました。')
        except Exception as e:
            messagebox.showerror('CSV読込エラー',str(e))

    def create_midi(self):
        self.open_midi_export()

    def create_midi_current(self,output_path=None):
        self.commit_current_view()
        mid=MidiFile(ticks_per_beat=TICKS_PER_BEAT)
        bpm=int(self.bpm_var.get())
        chord_track=MidiTrack()
        mid.tracks.append(chord_track)
        chord_track.append(MetaMessage('track_name',name='Chords'))
        chord_track.append(MetaMessage('set_tempo',tempo=bpm2tempo(bpm)))
        for chunk in self.encode_state_chunks():
            chord_track.append(MetaMessage('text',text=chunk,time=0))
        bass_track=MidiTrack()
        mid.tracks.append(bass_track)
        bass_track.append(MetaMessage('track_name',name='Bass'))
        # General MIDI: Electric Bass (finger) = program 34 (mido is 0-based, so 33)
        bass_track.append(Message('program_change',program=33,channel=1,time=0))
        last=self.last_bar()
        if last<0:
            messagebox.showwarning('MIDI作成','入力されたデータがありません。')
            return

        for bar_index in range(last+1):
            b=self.data[bar_index]
            if not b.split:
                notes=chord_notes(b.chord,b.octave)
                if notes:
                    for n in notes:
                        chord_track.append(Message('note_on',note=n,velocity=70,time=0))
                    chord_track.append(Message('note_off',note=notes[0],velocity=0,time=TICKS_PER_BEAT*4))
                    for n in notes[1:]:
                        chord_track.append(Message('note_off',note=n,velocity=0,time=0))
                else:
                    chord_track.append(Message('note_off',note=0,velocity=0,time=TICKS_PER_BEAT*4))
            else:
                for chord,octv in [(b.chord_1_2,b.octave_1_2),(b.chord_3_4,b.octave_3_4)]:
                    notes=chord_notes(chord,octv)
                    if notes:
                        for n in notes:
                            chord_track.append(Message('note_on',note=n,velocity=70,time=0))
                        chord_track.append(Message('note_off',note=notes[0],velocity=0,time=TICKS_PER_BEAT*2))
                        for n in notes[1:]:
                            chord_track.append(Message('note_off',note=n,velocity=0,time=0))
                    else:
                        chord_track.append(Message('note_off',note=0,velocity=0,time=TICKS_PER_BEAT*2))

            sub=RESOLUTIONS[b.resolution] if b.resolution in RESOLUTIONS else RESOLUTIONS[self.res_var.get()]
            ticks_per_note=TICKS_PER_BEAT//sub
            bass_values=list(b.bass)
            while len(bass_values)<sub*4:
                bass_values.append('')
            for s in bass_values[:sub*4]:
                s=normalize_note(s,self.auto_low_var.get(),self.auto_high_var.get())
                n=auto_midi(s,self.auto_low_var.get(),self.auto_high_var.get()) if s and s!='-' else None
                if n is not None:
                    bass_track.append(Message('note_on',note=n,velocity=80,channel=1,time=0))
                    bass_track.append(Message('note_off',note=n,velocity=0,channel=1,time=ticks_per_note))
                else:
                    bass_track.append(Message('note_off',note=0,velocity=0,channel=1,time=ticks_per_note))

        path=output_path
        if not path:
            path=filedialog.asksaveasfilename(defaultextension='.mid',filetypes=[('MIDI','*.mid')])
            if not path:return
        try:
            mid.save(path)
            self.midi_path=path
            messagebox.showinfo('MIDI作成',f'MIDIを作成しました。\n{path}')
        except Exception as e:
            messagebox.showerror('MIDI作成エラー',str(e))

    def play_midi(self):
        if not self.midi_path:
            messagebox.showwarning('MIDI再生','先にMIDIを作成してください。')
            return
        self.stop_midi()
        try:
            if sys.platform.startswith('win'):
                self.player_process=subprocess.Popen(['cmd','/c','start','','{}'.format(self.midi_path)],shell=False)
            elif sys.platform=='darwin':
                self.player_process=subprocess.Popen(['open',self.midi_path])
            else:
                player=shutil.which('xdg-open')
                if player:
                    self.player_process=subprocess.Popen([player,self.midi_path])
        except Exception as e:
            messagebox.showerror('MIDI再生エラー',str(e))

    def stop_midi(self):
        if self.player_process is not None:
            try:
                self.player_process.terminate()
            except Exception:
                pass
            self.player_process=None

if __name__=='__main__':
    root=tk.Tk()
    app=App(root)
    root.mainloop()
