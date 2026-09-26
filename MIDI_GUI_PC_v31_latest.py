import csv
import json
import base64
import zlib
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pathlib import Path
import subprocess
import sys
import shutil
import os
import re
import copy
from mido import MidiFile, MidiTrack, Message, MetaMessage, bpm2tempo, tempo2bpm

TICKS_PER_BEAT = 480
BEATS_PER_BAR = 4
DEFAULT_BPM = 120
DEFAULT_BARS = 64
VISIBLE_BARS = 4
MIN_VISIBLE_BARS = 1
MAX_VISIBLE_BARS = 32

ROOTS = ['C','C#','D','Eb','E','F','F#','G','G#','A','Bb','B']
KEYS = ROOTS + [r+'m' for r in ROOTS]
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
        self.split_1_2=False
        self.split_3_4=False
        self.chord_1=''; self.octave_1=3
        self.chord_2=''; self.octave_2=3
        self.chord_3=''; self.octave_3=3
        self.chord_4=''; self.octave_4=3
        self.on_bass=''
        self.on_bass_1_2=''; self.on_bass_3_4=''
        self.on_bass_1=''; self.on_bass_2=''; self.on_bass_3=''; self.on_bass_4=''
        self.resolution=''  # 空欄ならTrackの分解能を継承
        self.bass=[]
        self.bass_grid=[]
        self.bass_grid_base=''

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

def midi_to_note_name(midi,accidental='sharp'):
    names=FLAT_NAMES if accidental=='flat' else SHARP_NAMES
    return f"{names[midi%12]}{midi//12-1}"

def parse_key(key):
    key=(key or '').strip()
    is_minor=key.endswith('m')
    tonic=key[:-1] if is_minor else key
    tonic_pc,_=parse_note(tonic)
    return tonic_pc,is_minor

def degree(note,key):
    note=(note or '').strip()
    if not note or note=='-':
        return ''
    pc,_=parse_note(note)
    key_pc,is_minor=parse_key(key)
    if pc is None or key_pc is None:
        return ''
    interval=(NOTE_TO_PC[pc]-NOTE_TO_PC[key_pc])%12
    names=DEGREE_NAMES_FLAT if ('b' in pc or is_minor) else DEGREE_NAMES_SHARP
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

def slash_bass_midi(on_bass, chord_note_midis):
    on_bass=(on_bass or '').strip()
    if not on_bass or not chord_note_midis:return None
    pc,_=parse_note(on_bass)
    if pc is None:return None
    target=NOTE_TO_PC[pc]
    n=min(chord_note_midis)
    while n%12!=target:n-=1
    return n

def chord_notes_with_slash(chord,octv,on_bass=''):
    notes=chord_notes(chord,octv)
    if not notes:return []
    bass=slash_bass_midi(on_bass,notes)
    return sorted(set(notes if bass is None else [bass]+notes))

def make_bass_grid_from_legacy(values,res_name):
    """ベース分解能を親階層として初期セルを作る。"""
    sub=RESOLUTIONS.get(res_name,1)
    slots=sub*BEATS_PER_BAR
    vals=list(values or [])
    while len(vals)<slots:vals.append('')
    vals=vals[:slots]
    grid=[]
    for slot,v in enumerate(vals):
        beat=slot//sub+1
        subpos=slot%sub+1
        base_path=[beat] if sub==1 else [beat,subpos]
        grid.append({'note':str(v or ''),'base_slot':slot,'path':base_path,'divisions':[]})
    return grid

def base_path_for_slot(slot,res_name):
    sub=RESOLUTIONS.get(res_name,1)
    beat=slot//sub+1
    subpos=slot%sub+1
    return [beat] if sub==1 else [beat,subpos]

def bass_path_label(item):
    return '.'.join(str(x) for x in item.get('path',[]))

def bass_segment_fraction(item):
    """親スロットに対する長さ比。divisions=[2,3]なら1/6。"""
    den=1
    for d in item.get('divisions',[]):
        try:
            d=int(d)
        except Exception:
            d=2
        den*=max(2,d)
    return 1/den

def bass_segment_ticks(item,res_name):
    sub=RESOLUTIONS.get(res_name,1)
    base_ticks=TICKS_PER_BEAT/sub
    return max(1,round(base_ticks*bass_segment_fraction(item)))

def bass_note_value_symbol(item,res_name):
    """音価表示。4分=♩、8分=♪、16分以降は文字化け回避のため数字。"""
    sub=RESOLUTIONS.get(res_name,1)
    base_level={1:0,2:1,4:2,8:3}.get(sub,0)
    divisions=[int(x) for x in item.get('divisions',[])]
    level=base_level+len(divisions)
    labels={0:'♩',1:'♪',2:'16',3:'32',4:'64',5:'128'}
    label=labels.get(level,str(2**(level+2)))
    if 3 in divisions:
        label+='³'
    return label

def normalize_bass_grid(grid,res_name):
    """旧v30形式も階層パス形式へ変換する。"""
    sub=RESOLUTIONS.get(res_name,1)
    slots=sub*BEATS_PER_BAR
    if not isinstance(grid,list) or not grid:
        return make_bass_grid_from_legacy([],res_name)

    # New hierarchical format.
    if all(isinstance(x,dict) and 'path' in x and 'base_slot' in x for x in grid):
        out=[]
        for x in grid:
            slot=max(0,min(slots-1,int(x.get('base_slot',0))))
            path=x.get('path',base_path_for_slot(slot,res_name))
            divisions=x.get('divisions',[])
            if not isinstance(path,list):path=base_path_for_slot(slot,res_name)
            if not isinstance(divisions,list):divisions=[]
            out.append({
                'note':str(x.get('note','')),
                'base_slot':slot,
                'path':[int(v) for v in path],
                'divisions':[max(2,int(v)) for v in divisions]
            })
        out.sort(key=lambda x:(x['base_slot'],x['path']))
        return out

    # Previous slot/level format.
    if all(isinstance(x,dict) and 'slot' in x for x in grid):
        grouped={}
        for x in grid:
            slot=max(0,min(slots-1,int(x.get('slot',0))))
            grouped.setdefault(slot,[]).append(x)
        out=[]
        for slot in range(slots):
            items=grouped.get(slot,[])
            if not items:
                out.append({'note':'','base_slot':slot,'path':base_path_for_slot(slot,res_name),'divisions':[]})
                continue
            # Infer binary level by number/order in the parent.
            n=len(items)
            level=0
            while 2**level<n:level+=1
            for i,x in enumerate(items):
                suffix=[]
                temp=i
                for _ in range(level):
                    suffix.insert(0,temp%2+1)
                    temp//=2
                out.append({
                    'note':str(x.get('note','')),
                    'base_slot':slot,
                    'path':base_path_for_slot(slot,res_name)+suffix,
                    'divisions':[2]*level
                })
        return out

    # Old units format fallback.
    return make_bass_grid_from_legacy(
        [str(x.get('note','')) for x in grid if isinstance(x,dict)],
        res_name
    )

class App:
    def __init__(self,root):
        self.root=root
        self.root.bind('<Command-t>',self.shortcut_add_track)
        self.root.bind('<Control-t>',self.shortcut_add_track)
        self.root.title('Bass MIDI GUI PC v31')
        self.root.geometry('1440x900')
        self.root.minsize(1180,650)
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
        self.default_key_var=tk.StringVar(value='C')
        self.batch_key_var=tk.StringVar(value='C')
        self.batch_chord_var=tk.StringVar(value='')
        self.midi_path=None
        self.temp_work_path=Path.home()/'.bass_midi_gui_pc_work.json'
        self.player_process=None
        self._bar_clipboard=None
        style=ttk.Style()
        style.configure('TButton',padding=(8,5))
        style.configure('TCombobox',padding=(1,1))
        style.configure('TEntry',padding=(1,1))
        style.configure('Bar.TLabelframe.Label',font=('',12,'bold'))
        style.configure('BarLabel.TLabel',font=('',11))
        style.configure('BarBold.TLabel',font=('',11,'bold'))
        style.configure('Bar.TCombobox',font=('',11),padding=(4,5,4,5))
        style.configure('Bar.TEntry',font=('',11),padding=(4,5,4,5))
        style.configure('BassMini.TButton',padding=(0,0),font=('',12,'bold'))
        self.build_top()
        self.render()

    def rebuild_editor_screen(self):
        """サブ画面から通常編集画面へ安全に戻す共通処理。"""
        # 旧画面を完全破棄
        for w in self.root.winfo_children():
            try:w.destroy()
            except:pass
        self.widgets=[]
        self.committers=[]
        self.input_focus_widgets=[]
        # データ側を先に確定。UI変数は既存のTk変数を使う。
        self.current_track=max(0,min(self.current_track,len(self.tracks)-1))
        t=self.tracks[self.current_track]
        self.data=t['bars']
        self.bars_var.set(len(self.data))
        self.bpm_var.set(int(t.get('bpm',DEFAULT_BPM)))
        self.res_var.set(t.get('resolution','4分音符'))
        self.auto_low_var.set(t.get('auto_low','G2'))
        self.auto_high_var.set(t.get('auto_high','F#3'))
        self.page=max(0,min(self.page,max(0,(len(self.data)-1)//max(1,self.get_visible_bars()))))
        # UIを新規作成してから、UI依存値を反映
        self.build_top()
        self.track_name_var.set(t.get('name',f'JBR_{self.current_track+1:02d}_'))
        self.refresh_track_box()
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
        top2=ttk.Frame(self.root)
        top2.pack(fill='x',padx=8,pady=(0,6))
        ttk.Label(top2,text='自動音域').pack(side='left',padx=(0,3))
        auto_low_entry=ttk.Entry(top2,textvariable=self.auto_low_var,width=5)
        auto_low_entry.pack(side='left',padx=2)
        ttk.Label(top2,text='～').pack(side='left')
        auto_high_entry=ttk.Entry(top2,textvariable=self.auto_high_var,width=5)
        auto_high_entry.pack(side='left',padx=2)
        auto_low_entry.bind('<FocusOut>',lambda e:self.adjust_auto_range('low'))
        auto_high_entry.bind('<FocusOut>',lambda e:self.adjust_auto_range('high'))
        auto_low_entry.bind('<Return>',lambda e:self.adjust_auto_range('low'))
        auto_high_entry.bind('<Return>',lambda e:self.adjust_auto_range('high'))
        ttk.Label(top2,text='デフォルトKey').pack(side='left',padx=(12,3))
        default_key_box=ttk.Combobox(top2,textvariable=self.default_key_var,values=KEYS,state='readonly',width=5)
        default_key_box.pack(side='left',padx=2)
        ttk.Button(top2,text='全体へ適用',command=self.default_key_apply).pack(side='left',padx=2)
        ttk.Label(top2,text='表示8小節Key一括').pack(side='left',padx=(12,3))
        key_box=ttk.Combobox(top2,textvariable=self.batch_key_var,values=KEYS,state='readonly',width=5)
        key_box.pack(side='left',padx=2)
        ttk.Button(top2,text='適用',command=self.batch_key_apply).pack(side='left',padx=2)
        ttk.Label(top2,text='表示4小節コード一括').pack(side='left',padx=(12,3))
        chord_box=ttk.Combobox(top2,textvariable=self.batch_chord_var,values=CHORDS,width=12,state='readonly')
        chord_box.pack(side='left',padx=2)
        ttk.Button(top2,text='適用',command=self.batch_chord_apply).pack(side='left',padx=2)
        nav=ttk.Frame(self.root)
        nav.pack(fill='x',padx=8,pady=(0,6))
        self.prev_button=ttk.Button(nav,text='← 前の小節',command=lambda:self.move_page(-1))
        self.prev_button.pack(side='left',padx=3)
        self.next_button=ttk.Button(nav,text='次の小節 →',command=lambda:self.move_page(1))
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
        original=self.current_track
        try:
            for i in indices:
                self.current_track=i
                self.load_track_settings()
                path=os.path.join(folder,self.safe_midi_filename(self.tracks[i].get('name'),i))
                self.create_midi_current(path)
        finally:
            self.current_track=max(0,min(original,len(self.tracks)-1))
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
            idx=self.current_track
            win.destroy()
            self.export_midi_tracks([idx])
        ttk.Button(buttons,text='チェックしたExを出力',command=checked).pack(side='left',padx=3)
        ttk.Button(buttons,text='全Exを出力',command=all_ex).pack(side='left',padx=3)
        ttk.Button(buttons,text='編集中Exのみ',command=current_ex).pack(side='left',padx=3)

    def open_file_menu(self):
        """同じメインウインドウ内でファイル操作ページへ移動する。"""
        self.commit_current_view()
        self.sync_track_settings()
        self._file_menu_active=True
        # callback中は編集画面を破棄せず、一時的に非表示にする。
        for w in list(self.root.winfo_children()):
            manager=w.winfo_manager()
            if manager=='pack':
                w.pack_forget()
            elif manager=='grid':
                w.grid_remove()
        self.render_file_menu_page()
    def render_file_menu_page(self):
        """ファイル操作をメインウインドウ内の1ページとして表示する。"""
        page=ttk.Frame(self.root,padding=(24,18))
        self._file_menu_page=page
        page.pack(fill='both',expand=True)

        top=ttk.Frame(page)
        top.pack(fill='x',pady=(0,18))
        ttk.Button(top,text='← 編集画面に戻る',command=self.close_file_menu).pack(side='left')
        ttk.Label(top,text='ファイル',font=('',18,'bold')).pack(side='left',padx=18)

        # gridだけに依存せず、縦並びで確実に全操作を表示する。
        body=ttk.Frame(page)
        body.pack(fill='both',expand=True)
        body.columnconfigure(0,weight=1)
        body.columnconfigure(1,weight=0)
        body.columnconfigure(2,weight=0)
        body.columnconfigure(3,weight=1)

        style=ttk.Style()
        style.configure('FileBig.TButton',font=('',19,'bold'),padding=(4,10))

        def file_button(parent,row,text,command):
            parent.columnconfigure(0,weight=1)
            hit=ttk.Frame(parent,padding=(4,5))
            hit.grid(row=row,column=0,sticky='ew',pady=2)
            btn=ttk.Button(hit,text=text,command=command,style='FileBig.TButton')
            btn.pack(fill='x')
            hit.bind('<Button-1>',lambda e,c=command:c())
            return btn

        load_col=ttk.LabelFrame(body,text='読み込み・再生',padding=8)
        load_col.grid(row=0,column=1,padx=(0,6),pady=4,sticky='ns')
        file_button(load_col,0,'一時保存読込',self.load_temp_work)
        file_button(load_col,1,'プロジェクト読込',self.load_project)
        file_button(load_col,2,'MIDI読込',self.load_midi)
        file_button(load_col,3,'MIDI再生',self.play_midi)
        file_button(load_col,4,'停止',self.stop_midi)
        file_button(load_col,5,'CSV読込',self.load_csv)

        save_col=ttk.LabelFrame(body,text='保存・出力',padding=8)
        save_col.grid(row=0,column=2,padx=(6,0),pady=4,sticky='ns')
        file_button(save_col,0,'一時保存',self.save_temp_work)
        file_button(save_col,1,'プロジェクト保存',self.save_project)
        file_button(save_col,2,'MIDI出力',self.open_midi_export)
        file_button(save_col,3,'CSV保存',self.save_csv)

    def close_file_menu(self):
        """ファイルページから通常編集画面へ戻る。"""
        self._file_menu_active=False
        self.root.after_idle(self.rebuild_editor_screen)

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
        """同じメインウインドウのトラック構成ページへ移動する。"""
        self.commit_current_view()
        self.sync_track_settings()
        self._track_config_page_no=0
        self._track_config_active=True
        self.root.after_idle(self._show_track_config_page)

    def _show_track_config_page(self):
        self.widgets=[]
        self.committers=[]
        self.render_track_config_page()

    def render_track_config_page(self):
        """トラック構成ページ全体をメインウインドウに描画する。"""
        self.renumber_tracks()
        for w in list(self.root.winfo_children()):
            try:w.destroy()
            except:pass
        page=ttk.Frame(self.root,padding=(24,18))
        page.pack(fill='both',expand=True)

        top=ttk.Frame(page)
        top.pack(fill='x',pady=(0,12))
        ttk.Button(top,text='← 編集画面に戻る',command=self.close_track_config).pack(side='left')
        ttk.Label(top,text='トラック構成',font=('',18,'bold')).pack(side='left',padx=18)
        ttk.Button(top,text='+ トラック追加',command=self.add_track_from_config).pack(side='right')
        undo=ttk.Button(top,text='元に戻す',command=self.undo_delete_from_config)
        undo.pack(side='right',padx=8)
        if not getattr(self,'_last_deleted_track',None):undo.state(['disabled'])

        page_size=8
        total=max(1,(len(self.tracks)+page_size-1)//page_size)
        self._track_config_page_no=max(0,min(self._track_config_page_no,total-1))
        start=self._track_config_page_no*page_size
        end=min(start+page_size,len(self.tracks))

        nav=ttk.Frame(page)
        nav.pack(fill='x',pady=(0,12))
        prev=ttk.Button(nav,text='◀ 前へ',command=lambda:self.change_track_config_page(-1))
        prev.pack(side='left')
        ttk.Label(nav,text=f'{self._track_config_page_no+1} / {total}',anchor='center',font=('',11)).pack(side='left',fill='x',expand=True)
        nxt=ttk.Button(nav,text='次へ ▶',command=lambda:self.change_track_config_page(1))
        nxt.pack(side='right')
        if self._track_config_page_no<=0:prev.state(['disabled'])
        if self._track_config_page_no>=total-1:nxt.state(['disabled'])

        merge=ttk.LabelFrame(page,text='Ex結合',padding=(10,7))
        merge.pack(fill='x',pady=(0,12))
        merge_values=[f'Ex {i+1:02d}  {t.get("name") or f"JBR_{i+1:02d}_"}' for i,t in enumerate(self.tracks)]
        if not hasattr(self,'_merge_source_var'):self._merge_source_var=tk.StringVar()
        if not hasattr(self,'_merge_target_var'):self._merge_target_var=tk.StringVar()
        if self._merge_source_var.get() not in merge_values:self._merge_source_var.set(merge_values[0] if merge_values else '')
        if self._merge_target_var.get() not in merge_values:self._merge_target_var.set(merge_values[1] if len(merge_values)>1 else (merge_values[0] if merge_values else ''))
        ttk.Label(merge,text='結合元').pack(side='left')
        ttk.Combobox(merge,textvariable=self._merge_source_var,values=merge_values,state='readonly',width=28).pack(side='left',padx=(4,10))
        ttk.Label(merge,text='→ 結合先').pack(side='left')
        ttk.Combobox(merge,textvariable=self._merge_target_var,values=merge_values,state='readonly',width=28).pack(side='left',padx=(4,10))
        ttk.Label(merge,text='の後ろへ').pack(side='left',padx=(0,8))
        merge_btn=ttk.Button(merge,text='結合',command=self.merge_tracks_from_config)
        merge_btn.pack(side='left')
        undo_merge=ttk.Button(merge,text='結合を元に戻す',command=self.undo_merge_from_config)
        undo_merge.pack(side='left',padx=(8,0))
        if len(self.tracks)<2:merge_btn.state(['disabled'])
        if not getattr(self,'_last_merge_state',None):undo_merge.state(['disabled'])

        table=ttk.Frame(page)
        table.pack(fill='both',expand=True)
        table.columnconfigure(1,weight=1)
        ttk.Label(table,text='Ex',anchor='center',font=('',12,'bold')).grid(row=0,column=0,padx=(4,12),pady=(0,10),sticky='ew')
        ttk.Label(table,text='トラック名',anchor='w',font=('',12,'bold')).grid(row=0,column=1,padx=8,pady=(0,10),sticky='ew')
        ttk.Label(table,text='入力済小節',anchor='center',font=('',12,'bold')).grid(row=0,column=2,padx=12,pady=(0,10),sticky='ew')
        ttk.Label(table,text='',width=10).grid(row=0,column=3)
        self._track_name_vars=[]
        for r,i in enumerate(range(start,end),start=1):
            ttk.Label(table,text=f'Ex {i+1:02d}',anchor='center',font=('',11)).grid(row=r,column=0,padx=(4,12),pady=7,sticky='ew')
            v=tk.StringVar(value=self.tracks[i].get('name') or f'JBR_{i+1:02d}_')
            self._track_name_vars.append((i,v))
            ent=ttk.Entry(table,textvariable=v,font=('',12))
            ent.grid(row=r,column=1,padx=8,pady=7,ipady=6,sticky='ew')
            ent.bind('<FocusOut>',lambda e,idx=i,var=v:self.save_track_name_from_config(idx,var))
            ent.bind('<Return>',lambda e,idx=i,var=v:self.save_track_name_from_config(idx,var))
            ttk.Label(table,text=str(self.track_input_bar_count(self.tracks[i])),anchor='center',font=('',11)).grid(row=r,column=2,padx=12,pady=7,sticky='ew')
            ttk.Button(table,text='削除',command=lambda idx=i:self.delete_track_from_config(idx)).grid(row=r,column=3,padx=(8,4),pady=7,sticky='ew')

    def save_track_name_from_config(self,idx,var):
        if 0<=idx<len(self.tracks):
            self.tracks[idx]['name']=var.get()

    def save_visible_track_names(self):
        for idx,var in getattr(self,'_track_name_vars',[]):
            if 0<=idx<len(self.tracks):
                self.tracks[idx]['name']=var.get()

    def close_track_config(self):
        """トラック構成ページから通常編集画面へ戻る。"""
        self.save_visible_track_names()
        self._track_config_active=False
        self.root.after_idle(self.rebuild_editor_screen)

    def change_track_config_page(self,delta):
        self.save_visible_track_names()
        self._track_config_page_no+=delta
        self.root.after_idle(self.render_track_config_page)

    def add_track_from_config(self):
        self.save_visible_track_names()
        no=max([int(t.get('no',0)) for t in self.tracks]+[0])+1
        bars=[Bar() for _ in range(DEFAULT_BARS)]
        self.tracks.append({'no':no,'name':f'JBR_{no:02d}_','bpm':DEFAULT_BPM,'resolution':'4分音符','auto_low':'G2','auto_high':'F#3','bars':bars})
        self.current_track=len(self.tracks)-1
        self._track_config_page_no=(len(self.tracks)-1)//8
        self.root.after_idle(self.render_track_config_page)

    def delete_track_from_config(self,idx):
        self.save_visible_track_names()
        if len(self.tracks)<=1:
            messagebox.showwarning('削除','最後の1トラックは削除できません。',parent=self.root)
            return
        label=self.tracks[idx].get('name') or f'JBR_{idx+1:02d}_'
        if not messagebox.askokcancel('削除確認',f'Ex {idx+1:02d}「{label}」を削除します。',parent=self.root):
            return
        self._last_deleted_track=(idx,self.tracks[idx])
        del self.tracks[idx]
        self.renumber_tracks()
        if self.current_track>=len(self.tracks):self.current_track=len(self.tracks)-1
        self._track_config_page_no=min(self._track_config_page_no,max(0,(len(self.tracks)-1)//8))
        self.render_track_config_page()

    def undo_delete_from_config(self):
        item=getattr(self,'_last_deleted_track',None)
        if not item:return
        self.save_visible_track_names()
        idx,track=item
        idx=max(0,min(idx,len(self.tracks)))
        self.tracks.insert(idx,track)
        self.renumber_tracks()
        self._last_deleted_track=None
        self._track_config_page_no=idx//8
        self.render_track_config_page()

    def _merge_selection_index(self,value):
        m=re.match(r'^Ex\s+(\d+)',value or '')
        if not m:return None
        idx=int(m.group(1))-1
        return idx if 0<=idx<len(self.tracks) else None

    def merge_tracks_from_config(self):
        self.save_visible_track_names()
        src=self._merge_selection_index(self._merge_source_var.get())
        dst=self._merge_selection_index(self._merge_target_var.get())
        if src is None or dst is None or src==dst:
            messagebox.showwarning('Ex結合','異なる結合元Exと結合先Exを選択してください。',parent=self.root)
            return
        src_name=self.tracks[src].get('name') or f'JBR_{src+1:02d}_'
        dst_name=self.tracks[dst].get('name') or f'JBR_{dst+1:02d}_'
        if not messagebox.askokcancel(
            'Ex結合確認',
            f'Ex {src+1:02d}「{src_name}」を\nEx {dst+1:02d}「{dst_name}」の後ろへ結合します。\n\n結合元Exは一覧から削除されます。',
            parent=self.root):
            return
        # 直前1回だけ完全に戻せるよう、リスト構造と結合先小節数を保存。
        self._last_merge_state={
            'src_index':src,'dst_index':dst,'src_track':self.tracks[src],
            'dst_track':self.tracks[dst],'dst_bar_count':len(self.tracks[dst].get('bars',[])),
            'current_track':self.current_track
        }
        src_track=self.tracks[src]
        dst_track=self.tracks[dst]
        # Barオブジェクトをそのまま連結するのでKey/コード分割/分解能/Bass等を全保持。
        dst_track['bars'].extend(src_track.get('bars',[]))
        del self.tracks[src]
        self.renumber_tracks()
        # 削除により結合先indexが前へずれる場合を補正。
        new_dst=dst-1 if src<dst else dst
        self.current_track=max(0,min(new_dst,len(self.tracks)-1))
        self._track_config_page_no=self.current_track//8
        self._merge_source_var.set('')
        self._merge_target_var.set('')
        self.render_track_config_page()

    def undo_merge_from_config(self):
        state=getattr(self,'_last_merge_state',None)
        if not state:return
        self.save_visible_track_names()
        src_index=state['src_index']
        dst_track=state['dst_track']
        dst_bar_count=state['dst_bar_count']
        # 結合時に追加した小節だけを結合先から除去。
        dst_track['bars']=dst_track.get('bars',[])[:dst_bar_count]
        # 元Exを元の位置へ復帰。
        insert_at=max(0,min(src_index,len(self.tracks)))
        self.tracks.insert(insert_at,state['src_track'])
        self.renumber_tracks()
        self.current_track=max(0,min(state['current_track'],len(self.tracks)-1))
        self._last_merge_state=None
        self._track_config_page_no=insert_at//8
        self._merge_source_var.set('')
        self._merge_target_var.set('')
        self.render_track_config_page()

    def renumber_tracks(self):
        """現在の並び順を正としてEx番号を01,02,...へ再配番する。"""
        for i,t in enumerate(self.tracks):
            t['no']=i+1

    def refresh_track_box(self):
        if not hasattr(self,'track_box'):
            return
        self.renumber_tracks()
        vals=[f"{i+1:02d}" for i in range(len(self.tracks))]
        self.track_box['values']=vals
        if vals:
            self.track_var.set(vals[self.current_track])

    def sync_track_settings(self):
        if not self.tracks:
            return
        t=self.tracks[self.current_track]
        t['name']=self.track_name_var.get().strip() or f"JBR_{int(t.get('no',self.current_track+1)):02d}_"
        t['bpm']=int(self.bpm_var.get())
        t['resolution']=self.res_var.get()
        t['auto_low']=self.auto_low_var.get()
        t['auto_high']=self.auto_high_var.get()
        t['bars']=self.data

    def load_track_settings(self):
        t=self.tracks[self.current_track]
        self.data=t['bars']
        self.bars_var.set(len(self.data))
        self.track_name_var.set(t.get('name',f'JBR_{self.current_track+1:02d}_'))
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

    def adjust_auto_range(self,changed):
        low_text=self.auto_low_var.get().strip()
        high_text=self.auto_high_var.get().strip()
        low_pc,low_oct=parse_note(low_text)
        high_pc,high_oct=parse_note(high_text)
        if low_pc is None or low_oct is None or high_pc is None or high_oct is None:
            return
        low_midi=12*(low_oct+1)+NOTE_TO_PC[low_pc]
        high_midi=12*(high_oct+1)+NOTE_TO_PC[high_pc]
        if changed=='low':
            if high_midi<low_midi:
                high_midi=low_midi
            elif high_midi-low_midi>12:
                high_midi=low_midi+12
            else:
                return
            self.auto_high_var.set(midi_to_note_name(high_midi,'flat' if 'b' in high_text else 'sharp'))
        else:
            if low_midi>high_midi:
                low_midi=high_midi
            elif high_midi-low_midi>12:
                low_midi=high_midi-12
            else:
                return
            self.auto_low_var.set(midi_to_note_name(low_midi,'flat' if 'b' in low_text else 'sharp'))
        self.sync_track_settings()

    def default_key_apply(self):
        key=self.default_key_var.get()
        if not key:
            return
        # 表示中のGUI値を先に保存する。
        self.commit_current_view()
        self.sync_track_settings()
        # 表示中KeyのStringVarも新Keyへ更新する。
        # ボタンクリックに伴うFocusOut等が後から発生しても旧Keyへ戻らない。
        for b,key_var in getattr(self,'visible_key_vars',[]):
            key_var.set(key)
            b.key=key
        # 全Ex・全小節へ適用。
        for t in self.tracks:
            for b in t.get('bars',[]):
                b.key=key
        self.data=self.tracks[self.current_track]['bars']
        self.batch_key_var.set(key)
        self.committers=[]
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

    def copy_bar_to_clipboard(self,bar_index):
        """小節情報を丸ごとコピー。"""
        self.commit_current_view()
        if not (0<=bar_index<len(self.data)):return
        self._bar_clipboard=copy.deepcopy(self.data[bar_index])

    def paste_bar_from_clipboard(self,bar_index):
        """コピー済み小節を指定小節へ上書き貼り付け。"""
        if self._bar_clipboard is None or not (0<=bar_index<len(self.data)):return
        self.commit_current_view()
        self.data[bar_index]=copy.deepcopy(self._bar_clipboard)
        self.render()

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
        b.chord_1_2=cv(b.chord_1_2); b.chord_3_4=cv(b.chord_3_4)
        for n in range(1,5):
            setattr(b,f'chord_{n}',cv(getattr(b,f'chord_{n}',''))); setattr(b,f'on_bass_{n}',cv(getattr(b,f'on_bass_{n}','')))
        b.on_bass=cv(getattr(b,'on_bass','')); b.on_bass_1_2=cv(getattr(b,'on_bass_1_2','')); b.on_bass_3_4=cv(getattr(b,'on_bass_3_4',''))
        b.bass=[cv(x) for x in b.bass]
        for item in getattr(b,'bass_grid',[]):item['note']=cv(item.get('note',''))
        self.render()

    def render(self):
        self.commit_current_view()
        self.committers=[]
        self.visible_key_vars=[]
        self.input_focus_widgets=[]
        for w in self.widgets:
            w.destroy()
        self.widgets=[]
        visible=self.get_visible_bars()
        start=self.page*visible
        end=min(start+visible,len(self.data))
        self.page_label.config(text=f'{start+1}～{end}小節 / 全{len(self.data)}小節')
        container=ttk.Frame(self.root)
        container.pack(fill='both',expand=True,padx=2,pady=4)
        self.widgets.append(container)
        # 右上: 選択中Bass入力のミラー表示。横スクロール外でも内容を確認・編集できる。
        mirror=ttk.LabelFrame(container,text='選択中 Bass',padding=(4,3))
        mirror.grid(row=0,column=1,sticky='ne',padx=(2,2),pady=(0,3))
        self._bass_mirror_label_var=tk.StringVar(value='—')
        self._bass_mirror_value_var=tk.StringVar(value='')
        ttk.Label(mirror,textvariable=self._bass_mirror_label_var,font=('',11,'bold')).pack(side='left',padx=(0,6))
        mirror_entry=ttk.Entry(mirror,textvariable=self._bass_mirror_value_var,width=5,justify='center',style='Bar.TEntry')
        mirror_entry.pack(side='left',ipadx=4,ipady=3)
        self._bass_mirror_entry=mirror_entry
        self._bass_mirror_source_var=None
        self._bass_mirror_updating=False

        def mirror_to_source(*args):
            if self._bass_mirror_updating:return
            src=getattr(self,'_bass_mirror_source_var',None)
            if src is not None:
                try:src.set(self._bass_mirror_value_var.get())
                except:pass
        self._bass_mirror_value_var.trace_add('write',mirror_to_source)

        legend=ttk.Frame(container)
        legend.grid(row=0,column=0,sticky='w',padx=4,pady=(0,5))
        tk.Label(legend,text='● Keyから見た度数',fg='green',font=('',14,'bold')).pack(side='left',padx=(0,18))
        tk.Label(legend,text='● コードルートから見た度数',fg='purple',font=('',14,'bold')).pack(side='left')
        for c in range(2):
            container.columnconfigure(c,weight=1,uniform='barcols',minsize=560)
        for pos,i in enumerate(range(start,end)):
            row=pos//2+1
            col=pos%2
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
        frame.grid(row=row,column=col,sticky='nsew',padx=1,pady=2)
        frame.columnconfigure(0,weight=1)
        key=tk.StringVar(value=b.key); self.visible_key_vars.append((b,key))
        split=tk.BooleanVar(value=b.split); split12=tk.BooleanVar(value=getattr(b,'split_1_2',False)); split34=tk.BooleanVar(value=getattr(b,'split_3_4',False))
        chord=tk.StringVar(value=b.chord); c12=tk.StringVar(value=b.chord_1_2); c34=tk.StringVar(value=b.chord_3_4)
        c1=tk.StringVar(value=getattr(b,'chord_1','')); c2=tk.StringVar(value=getattr(b,'chord_2','')); c3=tk.StringVar(value=getattr(b,'chord_3','')); c4=tk.StringVar(value=getattr(b,'chord_4',''))
        ob=tk.StringVar(value=getattr(b,'on_bass','')); ob12=tk.StringVar(value=getattr(b,'on_bass_1_2','')); ob34=tk.StringVar(value=getattr(b,'on_bass_3_4',''))
        ob1=tk.StringVar(value=getattr(b,'on_bass_1','')); ob2=tk.StringVar(value=getattr(b,'on_bass_2','')); ob3=tk.StringVar(value=getattr(b,'on_bass_3','')); ob4=tk.StringVar(value=getattr(b,'on_bass_4',''))
        chord_oct=tk.IntVar(value=b.octave); oct12=tk.IntVar(value=b.octave_1_2); oct34=tk.IntVar(value=b.octave_3_4)
        oct1=tk.IntVar(value=getattr(b,'octave_1',3)); oct2=tk.IntVar(value=getattr(b,'octave_2',3)); oct3=tk.IntVar(value=getattr(b,'octave_3',3)); oct4=tk.IntVar(value=getattr(b,'octave_4',3))
        bar_res=tk.StringVar(value=b.resolution or 'Track')

        key_row=ttk.Frame(frame); key_row.grid(row=0,column=0,sticky='w',padx=3,pady=(2,1))
        ttk.Label(key_row,text='Key',style='BarLabel.TLabel').pack(side='left')
        key_box=ttk.Combobox(key_row,textvariable=key,values=KEYS,state='readonly',width=5,takefocus=False,style='Bar.TCombobox')
        key_box.pack(side='left',padx=(2,3),ipadx=3,ipady=2)
        ttk.Button(key_row,text='#/♭',width=2,command=lambda idx=index:self.toggle_bar_accidental(idx)).pack(side='left',padx=(0,3))
        ttk.Label(key_row,text='分解能',style='BarLabel.TLabel').pack(side='left',padx=(2,1))
        bar_res_box=ttk.Combobox(key_row,textvariable=bar_res,values=['Track']+list(RESOLUTIONS.keys()),state='readonly',width=7,takefocus=False); bar_res_box.pack(side='left',padx=(1,2))

        split_row=ttk.Frame(frame); split_row.grid(row=1,column=0,sticky='w',padx=3,pady=(0,1))
        split_cb=ttk.Checkbutton(split_row,text='2拍分割',variable=split,takefocus=False); split_cb.pack(side='left')
        cp=ttk.Frame(split_row); cp.pack(side='right',padx=(6,0))
        ttk.Button(cp,text='C',width=1,style='BassMini.TButton',command=lambda idx=index:self.copy_bar_to_clipboard(idx)).pack(side='left')
        ttk.Button(cp,text='P',width=1,style='BassMini.TButton',command=lambda idx=index:self.paste_bar_from_clipboard(idx)).pack(side='left',padx=(1,0))
        child=ttk.Frame(split_row); child.pack(side='left',padx=(5,0))
        split12_cb=ttk.Checkbutton(child,text='1-2拍を1拍分割',variable=split12,takefocus=False)
        split34_cb=ttk.Checkbutton(child,text='3-4拍を1拍分割',variable=split34,takefocus=False)

        chord_row=ttk.Frame(frame); chord_row.grid(row=2,column=0,sticky='ew',padx=0,pady=(1,2))
        chord_row.columnconfigure(0,weight=1)
        chord_area=ttk.Frame(chord_row); chord_area.grid(row=0,column=0,sticky='ew')
        for beat_col in range(4):
            chord_area.columnconfigure(beat_col,weight=1,uniform='chordbeats')
        ttk.Label(chord_area,text='Chord',style='BarLabel.TLabel').place(x=2,y=0)
        degree_labels=[]

        def chord_unit(parent,col,label,var,oct_var,onbass_var,span=1):
            unit=ttk.Frame(parent); unit.grid(row=0,column=col,columnspan=span,sticky='nw',padx=0)
            if label:
                ttk.Label(unit,text=label,font=('',13),anchor='w').pack(fill='x',pady=(0,0))
            else:
                ttk.Label(unit,text='',font=('',13)).pack(fill='x',pady=(0,0))
            line=ttk.Frame(unit); line.pack(anchor='w')
            box=ttk.Combobox(line,textvariable=var,values=CHORDS,width=4,height=18,takefocus=True,style='Bar.TCombobox',state='readonly')
            box.pack(side='left',padx=(0,1),ipadx=3,ipady=2)
            ttk.Spinbox(line,from_=0,to=8,textvariable=oct_var,width=2,takefocus=False).pack(side='left',padx=(0,1),ipady=2)
            ttk.Label(line,text='/',font=('',11,'bold')).pack(side='left')
            onbox=ttk.Entry(line,textvariable=onbass_var,width=2,justify='center',takefocus=True,style='Bar.TEntry')
            onbox.pack(side='left',ipadx=3,ipady=2)
            dg=ttk.Label(unit,text='',foreground='blue',anchor='w',font=('',13,'bold'))
            dg.pack(fill='x',pady=(0,0))
            degree_labels.append((var,dg))
            self.input_focus_widgets.extend([box,onbox])

        def rebuild_chords():
            for w in chord_area.winfo_children():w.destroy()
            degree_labels.clear()
            if not split.get():
                chord_unit(chord_area,0,'',chord,chord_oct,ob,span=4)
            else:
                if split12.get():
                    chord_unit(chord_area,0,'1拍',c1,oct1,ob1)
                    chord_unit(chord_area,1,'2拍',c2,oct2,ob2)
                else:
                    chord_unit(chord_area,0,'1-2拍',c12,oct12,ob12,span=2)
                if split34.get():
                    chord_unit(chord_area,2,'3拍',c3,oct3,ob3)
                    chord_unit(chord_area,3,'4拍',c4,oct4,ob4)
                else:
                    chord_unit(chord_area,2,'3-4拍',c34,oct34,ob34,span=2)
            refresh_chord_degrees()

        bass_outer=ttk.Frame(frame); bass_outer.grid(row=3,column=0,sticky='ew',padx=0,pady=(1,2))
        ttk.Label(bass_outer,text='Bass',font=('',10,'bold')).pack(anchor='w',pady=(0,0))
        canvas=tk.Canvas(bass_outer,height=120,highlightthickness=0)
        hbar=ttk.Scrollbar(bass_outer,orient='horizontal',command=canvas.xview); canvas.configure(xscrollcommand=hbar.set)
        canvas.pack(fill='x',expand=True); hbar.pack(fill='x')
        bass_host=ttk.Frame(canvas); win=canvas.create_window((0,0),window=bass_host,anchor='nw')
        for bc in range(4):
            bass_host.columnconfigure(bc,weight=1,uniform='bassbeats')
        def update_bass_scrollregion(event=None):
            canvas.configure(scrollregion=canvas.bbox('all'))
        def resize_bass_window(event):
            total_segments=len(getattr(b,'bass_grid',[]) or [])
            req=bass_host.winfo_reqwidth()
            if total_segments<=16:
                canvas.itemconfigure(win,width=event.width)
            else:
                canvas.itemconfigure(win,width=max(event.width,req))
            update_bass_scrollregion()
        bass_host.bind('<Configure>',update_bass_scrollregion)
        canvas.bind('<Configure>',resize_bass_window)

        effective_res=b.resolution if b.resolution in RESOLUTIONS else self.res_var.get()
        if not getattr(b,'bass_grid',None):
            b.bass_grid=make_bass_grid_from_legacy(b.bass,effective_res)
        else:
            b.bass_grid=normalize_bass_grid(b.bass_grid,effective_res)
        b.bass_grid_base=effective_res
        bass_vars=[]; bass_key_labels=[]; bass_chord_labels=[]

        def current_chord_for_slot(slot):
            sub=RESOLUTIONS.get(effective_res,1)
            beat=slot//sub+1
            if not split.get():return chord.get()
            if beat<=2:return (c1.get() if beat==1 else c2.get()) if split12.get() else c12.get()
            return (c3.get() if beat==3 else c4.get()) if split34.get() else c34.get()

        def rebuild_bass_grid():
            for w in bass_host.winfo_children():w.destroy()
            # 子ウィジェット破棄後に古いbeat_frame参照を再利用しない。
            if hasattr(bass_host,'_beat_frames'):
                delattr(bass_host,'_beat_frames')
            bass_vars.clear(); bass_key_labels.clear(); bass_chord_labels.clear()
            b.bass_grid=normalize_bass_grid(b.bass_grid,effective_res)
            sub=RESOLUTIONS.get(effective_res,1)
            slots=sub*BEATS_PER_BAR

            # 常に1行表示。Bass側もChordと同じ4拍グリッドに合わせる。
            # 各拍の中をベース分解能ぶんだけ等分する。
            for beat_col in range(4):
                bass_host.columnconfigure(beat_col,weight=1,uniform='bassbeats')

            for slot in range(slots):
                display_row=0
                beat_col=slot//sub
                sub_col=slot%sub

                base_path=base_path_for_slot(slot,effective_res)
                base_label='.'.join(str(x) for x in base_path)
                base_item={'path':base_path,'divisions':[]}
                # beat_frame aligns to chord beat columns; subslots sit inside each beat.
                beat_frames=getattr(bass_host,'_beat_frames',None)
                if beat_frames is None:
                    beat_frames=[]
                    for bc in range(4):
                        bf=tk.Frame(bass_host,bg='white')
                        bf.grid(row=0,column=bc,sticky='nsew',padx=0,pady=0)
                        for sc in range(sub):
                            bf.columnconfigure(sc,weight=1,uniform=f'basssub{bc}')
                        beat_frames.append(bf)
                    bass_host._beat_frames=beat_frames
                beat_frame=beat_frames[beat_col]

                group=tk.Frame(beat_frame,bg='white',bd=1,relief='solid')
                group.grid(row=0,column=sub_col,padx=0,pady=0,sticky='nsew')
                head=tk.Frame(group,bg='white')
                head.grid(row=0,column=0,columnspan=99,sticky='w')
                tk.Label(head,text=base_label,font=('',9),bg='white').pack(side='left')
                tk.Label(
                    head,
                    text=bass_note_value_symbol(base_item,effective_res),
                    font=('',9,'bold'),
                    fg='#d94b72',
                    bg='white'
                ).pack(side='left',padx=(2,0))

                segments=[(idx,x) for idx,x in enumerate(b.bass_grid) if int(x.get('base_slot',-1))==slot]
                total_segments=max(1,len(b.bass_grid))
                # 細分化が進むほどセルを少し圧縮。極端に潰れない範囲で段階調整。
                if total_segments<=8:
                    note_width=2; label_font=8; degree_widths=(2,2); btn_scale=0.90
                elif total_segments<=16:
                    # 16音までは小節欄内に収めることを優先。
                    note_width=1; label_font=7; degree_widths=(1,1); btn_scale=0.72
                else:
                    # 17音以上は横スクロール前提でさらに圧縮。
                    note_width=1; label_font=7; degree_widths=(1,1); btn_scale=0.66

                for local,(idx,item) in enumerate(segments):
                    cell=tk.Frame(group,bg='white',bd=0,highlightthickness=0)
                    cell.grid(row=0,column=local,padx=0,pady=0,sticky='n')

                    # 分割後は 1.1.1 のすぐ右に音価をピンク寄りの赤で表示。
                    full_label=bass_path_label(item)
                    if full_label!=base_label:
                        child_head=tk.Frame(cell,bg='white')
                        child_head.pack(pady=0)
                        tk.Label(child_head,text=full_label,font=('',label_font),bg='white').pack(side='left')
                        tk.Label(
                            child_head,
                            text=bass_note_value_symbol(item,effective_res),
                            font=('',label_font,'bold'),
                            fg='#d94b72',
                            bg='white'
                        ).pack(side='left',padx=(1,0))

                    vr=tk.StringVar(value=item.get('note',''))
                    ent=ttk.Entry(cell,textvariable=vr,width=note_width,justify='center',style='Bar.TEntry')
                    ent.pack(pady=0,ipadx=1,ipady=1)
                    ent.bind('<Return>',lambda e,v=vr:self.normalize_entry(v))
                    ent.bind('<FocusOut>',lambda e,v=vr:self.normalize_entry(v))

                    def select_bass_entry(event=None,v=vr,it=item):
                        self._bass_mirror_source_var=v
                        self._bass_mirror_updating=True
                        try:
                            self._bass_mirror_label_var.set(bass_path_label(it))
                            self._bass_mirror_value_var.set(v.get())
                        finally:
                            self._bass_mirror_updating=False

                    ent.bind('<FocusIn>',select_bass_entry)
                    # セルの余白も音名入力欄のクリック判定として利用。
                    cell.bind('<Button-1>',lambda e,w=ent:w.focus_set())

                    btns=tk.Frame(cell,bg='white'); btns.pack(pady=0)

                    def split23_button(parent,command2,command3,w=34,h=26,font_size=14):
                        # 2/3を1枚のCanvas内に統合。中央線のみで区切り、隙間は物理的に0。
                        cv=tk.Canvas(parent,width=w,height=h,highlightthickness=0,borderwidth=0)
                        cv.pack(side='left',padx=0,pady=0)
                        cv.create_rectangle(0,0,w-1,h-1)
                        mid=w/2
                        cv.create_line(mid,0,mid,h)
                        cv.create_text(mid/2,h/2,text='2',font=('',font_size,'bold'))
                        cv.create_text(mid+mid/2,h/2,text='3',font=('',font_size,'bold'))
                        def on_click(e):
                            if e.x<mid:command2()
                            else:command3()
                        cv.bind('<Button-1>',on_click)
                        return cv

                    def tiny_button(parent,text,command,w=12,h=16,font_size=11):
                        cv=tk.Canvas(parent,width=w,height=h,highlightthickness=0,borderwidth=0)
                        cv.pack(side='left',padx=0,pady=0)
                        cv.create_rectangle(0,0,w-1,h-1)
                        cv.create_text(w/2,h/2,text=text,font=('',font_size,'bold'))
                        cv.bind('<Button-1>',lambda e:command())
                        return cv

                    # 細分化が進んでも横幅を食い過ぎないよう、2/3全体で30～34px程度に抑える。
                    b23w=max(24,round(30*btn_scale))
                    b23h=max(22,round(24*btn_scale))
                    b23f=max(11,round(13*btn_scale))
                    split23_button(
                        btns,
                        lambda i=idx:self.split_bass_cell(b,i,2,rebuild_bass_grid),
                        lambda i=idx:self.split_bass_cell(b,i,3,rebuild_bass_grid),
                        w=b23w,h=b23h,font_size=b23f
                    )

                    can_merge=bool(item.get('divisions',[]))
                    if can_merge:
                        tiny_button(btns,'-',lambda i=idx:self.merge_bass_cell(b,i,rebuild_bass_grid),w=10,h=18,font_size=11)

                    degrees=tk.Frame(cell,bg='white'); degrees.pack(pady=0)
                    dgk=tk.Label(degrees,text='',fg='green',bg='white',width=degree_widths[0],anchor='e',font=('',14,'bold'))
                    dgk.pack(side='left',padx=(2,0),pady=0)
                    dgc=tk.Label(degrees,text='',fg='purple',bg='white',width=degree_widths[1],anchor='w',font=('',14,'bold'))
                    dgc.pack(side='left',padx=(0,0),pady=0)
                    for target in (degrees,dgk,dgc):
                        target.bind('<Button-1>',lambda e,w=ent:w.focus_set())

                    def source_to_mirror(*args,v=vr,it=item):
                        if getattr(self,'_bass_mirror_source_var',None) is v:
                            self._bass_mirror_updating=True
                            try:
                                self._bass_mirror_label_var.set(bass_path_label(it))
                                self._bass_mirror_value_var.set(v.get())
                            finally:
                                self._bass_mirror_updating=False
                    vr.trace_add('write',source_to_mirror)

                    bass_vars.append((idx,vr,slot))
                    bass_key_labels.append(dgk)
                    bass_chord_labels.append(dgc)
                    self.input_focus_widgets.append(ent)
            refresh_bass_degrees()

        def refresh_bass_degrees():
            for n,(idx,vr,slot) in enumerate(bass_vars):
                raw=vr.get().strip()
                bass_key_labels[n].config(text=degree(raw,key.get()))
                bass_chord_labels[n].config(text=chord_interval(raw,current_chord_for_slot(slot)))

        def refresh_chord_degrees(*args):
            for var,dg in degree_labels:dg.config(text=chord_degree(var.get(),key.get()))
            refresh_bass_degrees()

        def apply_bar_controls():
            b.key=key.get(); b.split=split.get(); b.split_1_2=split12.get() if split.get() else False; b.split_3_4=split34.get() if split.get() else False
            b.chord=chord.get().strip(); b.octave=chord_oct.get(); b.on_bass=ob.get().strip()
            b.chord_1_2=c12.get().strip(); b.octave_1_2=oct12.get(); b.on_bass_1_2=ob12.get().strip()
            b.chord_3_4=c34.get().strip(); b.octave_3_4=oct34.get(); b.on_bass_3_4=ob34.get().strip()
            for n,var,ovar,obvar in [(1,c1,oct1,ob1),(2,c2,oct2,ob2),(3,c3,oct3,ob3),(4,c4,oct4,ob4)]:
                setattr(b,f'chord_{n}',var.get().strip()); setattr(b,f'octave_{n}',ovar.get()); setattr(b,f'on_bass_{n}',obvar.get().strip())
            b.resolution='' if bar_res.get()=='Track' else bar_res.get()
            for idx,vr,_ in bass_vars:
                if idx<len(b.bass_grid):b.bass_grid[idx]['note']=vr.get().strip()
            # 旧形式bassは親スロット先頭音のみを保持。編集の正本はbass_grid。
            slots=RESOLUTIONS.get(effective_res,1)*BEATS_PER_BAR
            b.bass=[]
            for slot in range(slots):
                segs=[x for x in b.bass_grid if int(x.get('base_slot',-1))==slot]
                b.bass.append(segs[0].get('note','') if segs else '')
        self.committers.append(apply_bar_controls)

        def split_changed():
            apply_bar_controls()
            if split.get():
                split12_cb.pack(side='left',padx=(0,4)); split34_cb.pack(side='left')
            else:
                split12_cb.pack_forget(); split34_cb.pack_forget()
            rebuild_chords()
        def child_changed():apply_bar_controls(); rebuild_chords()
        def bar_res_changed(event=None):
            apply_bar_controls(); eff=bar_res.get() if bar_res.get() in RESOLUTIONS else self.res_var.get()
            b.bass_grid=make_bass_grid_from_legacy(b.bass,eff); b.bass_grid_base=eff; self.render()

        split_cb.configure(command=split_changed); split12_cb.configure(command=child_changed); split34_cb.configure(command=child_changed)
        bar_res_box.bind('<<ComboboxSelected>>',bar_res_changed)
        key_box.bind('<<ComboboxSelected>>',lambda e:refresh_chord_degrees())
        for var in (chord,c12,c34,c1,c2,c3,c4,key):var.trace_add('write',refresh_chord_degrees)
        if split.get():
            split12_cb.pack(side='left',padx=(0,4)); split34_cb.pack(side='left')
        rebuild_chords(); rebuild_bass_grid(); refresh_chord_degrees()

    def split_bass_cell(self,b,idx,parts,refresh=None):
        """選択セルを2分割または3分割。階層パスを維持する。"""
        grid=getattr(b,'bass_grid',[])
        if not (0<=idx<len(grid)):return
        parts=2 if int(parts)==2 else 3
        item=grid[idx]
        base_slot=int(item.get('base_slot',0))
        path=list(item.get('path',[]))
        divisions=list(item.get('divisions',[]))
        if len(divisions)>=6:return
        note=item.get('note','')
        children=[]
        for n in range(1,parts+1):
            children.append({
                'note':note if n==1 else '',
                'base_slot':base_slot,
                'path':path+[n],
                'divisions':divisions+[parts]
            })
        grid[idx:idx+1]=children
        if refresh:refresh()

    def merge_bass_cell(self,b,idx,refresh=None):
        """同じ親を持つ兄弟セル一式を1段戻す。"""
        grid=getattr(b,'bass_grid',[])
        if not (0<=idx<len(grid)):return
        item=grid[idx]
        path=list(item.get('path',[]))
        divisions=list(item.get('divisions',[]))
        if not divisions or len(path)<1:return
        parts=divisions[-1]
        parent_path=path[:-1]
        parent_divisions=divisions[:-1]
        base_slot=int(item.get('base_slot',0))
        sib_indices=[]
        for j,x in enumerate(grid):
            if int(x.get('base_slot',-1))!=base_slot:continue
            xp=list(x.get('path',[])); xd=list(x.get('divisions',[]))
            if len(xp)==len(path) and xp[:-1]==parent_path and xd==divisions:
                sib_indices.append(j)
        if len(sib_indices)!=parts:return
        sib_indices.sort()
        first=sib_indices[0]; last=sib_indices[-1]
        note=''
        for j in sib_indices:
            if grid[j].get('note',''):
                note=grid[j].get('note','')
                break
        grid[first:last+1]=[{
            'note':note,
            'base_slot':base_slot,
            'path':parent_path,
            'divisions':parent_divisions
        }]
        if refresh:refresh()

    def bar_to_dict(self,b):
        return {'key':b.key,'accidental':getattr(b,'accidental','sharp'),'split':b.split,'chord':b.chord,'octave':b.octave,
            'chord_1_2':b.chord_1_2,'octave_1_2':b.octave_1_2,'chord_3_4':b.chord_3_4,'octave_3_4':b.octave_3_4,
            'split_1_2':getattr(b,'split_1_2',False),'split_3_4':getattr(b,'split_3_4',False),
            'chord_1':getattr(b,'chord_1',''),'octave_1':getattr(b,'octave_1',3),
            'chord_2':getattr(b,'chord_2',''),'octave_2':getattr(b,'octave_2',3),
            'chord_3':getattr(b,'chord_3',''),'octave_3':getattr(b,'octave_3',3),
            'chord_4':getattr(b,'chord_4',''),'octave_4':getattr(b,'octave_4',3),
            'on_bass':getattr(b,'on_bass',''),'on_bass_1_2':getattr(b,'on_bass_1_2',''),'on_bass_3_4':getattr(b,'on_bass_3_4',''),
            'on_bass_1':getattr(b,'on_bass_1',''),'on_bass_2':getattr(b,'on_bass_2',''),'on_bass_3':getattr(b,'on_bass_3',''),'on_bass_4':getattr(b,'on_bass_4',''),
            'resolution':b.resolution,'bass':list(b.bass),'bass_grid':copy.deepcopy(getattr(b,'bass_grid',[])),'bass_grid_base':getattr(b,'bass_grid_base','')}

    def dict_to_bar(self,item):
        b=Bar(); b.key=item.get('key','C')
        b.accidental=item.get('accidental','sharp') or 'sharp'; b.split=bool(item.get('split',False)); b.chord=item.get('chord','')
        b.octave=int(item.get('octave',3)); b.chord_1_2=item.get('chord_1_2',''); b.octave_1_2=int(item.get('octave_1_2',3))
        b.chord_3_4=item.get('chord_3_4',''); b.octave_3_4=int(item.get('octave_3_4',3))
        b.split_1_2=bool(item.get('split_1_2',False)); b.split_3_4=bool(item.get('split_3_4',False))
        for n in range(1,5):
            setattr(b,f'chord_{n}',item.get(f'chord_{n}','')); setattr(b,f'octave_{n}',int(item.get(f'octave_{n}',3))); setattr(b,f'on_bass_{n}',item.get(f'on_bass_{n}',''))
        b.on_bass=item.get('on_bass',''); b.on_bass_1_2=item.get('on_bass_1_2',''); b.on_bass_3_4=item.get('on_bass_3_4','')
        b.resolution=item.get('resolution','') or ''
        bass=item.get('bass',[]); b.bass=['' if x is None else str(x) for x in bass] if isinstance(bass,list) else []
        grid=item.get('bass_grid',[])
        b.bass_grid=copy.deepcopy(grid) if isinstance(grid,list) else []
        b.bass_grid_base=item.get('bass_grid_base','') or ''
        return b

    def state_dict(self):
        self.commit_current_view(); self.sync_track_settings(); self.renumber_tracks()
        tracks=[]
        for t in self.tracks:
            tracks.append({'no':t['no'],'name':t['name'],'bpm':t['bpm'],'resolution':t['resolution'],
                'auto_low':t.get('auto_low','G2'),'auto_high':t.get('auto_high','F#3'),'bars':[self.bar_to_dict(b) for b in t['bars']]})
        return {'format':'bass-midi-gui-multitrack','format_version':3,'app':'Bass MIDI GUI PC','version':'31',
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
            self.root.title(f'Bass MIDI GUI PC v31 - {Path(path).name}')
            print(f'プロジェクト読込完了: {path}')
        except Exception as e:
            # エラー時もNSAlertを避け、Python自体が落ちないようにする。
            print(f'プロジェクト読込エラー: {type(e).__name__}: {e}')
            self.root.title(f'Bass MIDI GUI PC v31 - 読込エラー')

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
            has_chord=bool(b.chord.strip() or b.chord_1_2.strip() or b.chord_3_4.strip() or any(getattr(b,f'chord_{n}','').strip() for n in range(1,5)))
            has_bass=any(str(x).strip() and str(x).strip()!='-' for x in b.bass) or any(str(x.get('note','')).strip() and str(x.get('note','')).strip()!='-' for x in getattr(b,'bass_grid',[]))
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
            def append_chord_segment(chord_text,octv,beats,on_bass=''):
                notes=chord_notes_with_slash(chord_text,octv,on_bass)
                duration=TICKS_PER_BEAT*beats
                if notes:
                    for n in notes: chord_track.append(Message('note_on',note=n,velocity=70,time=0))
                    chord_track.append(Message('note_off',note=notes[0],velocity=0,time=duration))
                    for n in notes[1:]: chord_track.append(Message('note_off',note=n,velocity=0,time=0))
                else:
                    chord_track.append(Message('note_off',note=0,velocity=0,time=duration))
            if not b.split:
                append_chord_segment(b.chord,b.octave,4,getattr(b,'on_bass',''))
            else:
                if getattr(b,'split_1_2',False):
                    append_chord_segment(getattr(b,'chord_1',''),getattr(b,'octave_1',3),1,getattr(b,'on_bass_1',''))
                    append_chord_segment(getattr(b,'chord_2',''),getattr(b,'octave_2',3),1,getattr(b,'on_bass_2',''))
                else:
                    append_chord_segment(b.chord_1_2,b.octave_1_2,2,getattr(b,'on_bass_1_2',''))
                if getattr(b,'split_3_4',False):
                    append_chord_segment(getattr(b,'chord_3',''),getattr(b,'octave_3',3),1,getattr(b,'on_bass_3',''))
                    append_chord_segment(getattr(b,'chord_4',''),getattr(b,'octave_4',3),1,getattr(b,'on_bass_4',''))
                else:
                    append_chord_segment(b.chord_3_4,b.octave_3_4,2,getattr(b,'on_bass_3_4',''))

            effective_res=b.resolution if b.resolution in RESOLUTIONS else self.res_var.get()
            grid=getattr(b,'bass_grid',[])
            if grid:
                grid=normalize_bass_grid(grid,effective_res)
                i=0
                while i<len(grid):
                    raw=str(grid[i].get('note','')).strip()
                    duration=bass_segment_ticks(grid[i],effective_res)
                    if raw=='-':
                        bass_track.append(Message('note_off',note=0,velocity=0,channel=1,time=duration)); i+=1; continue
                    normalized=normalize_note(raw,self.auto_low_var.get(),self.auto_high_var.get())
                    n=auto_midi(normalized,self.auto_low_var.get(),self.auto_high_var.get()) if normalized else None
                    if n is not None:
                        dur=duration; j=i+1
                        while j<len(grid) and str(grid[j].get('note','')).strip()=='-':
                            dur+=bass_segment_ticks(grid[j],effective_res); j+=1
                        bass_track.append(Message('note_on',note=n,velocity=80,channel=1,time=0))
                        bass_track.append(Message('note_off',note=n,velocity=0,channel=1,time=dur)); i=j
                    else:
                        bass_track.append(Message('note_off',note=0,velocity=0,channel=1,time=duration)); i+=1
            else:
                sub=RESOLUTIONS[effective_res]; ticks_per_note=TICKS_PER_BEAT//sub
                bass_values=list(b.bass)
                while len(bass_values)<sub*4:bass_values.append('')
                bass_values=bass_values[:sub*4]; i=0
                while i<len(bass_values):
                    raw=bass_values[i].strip()
                    if raw=='-':
                        bass_track.append(Message('note_off',note=0,velocity=0,channel=1,time=ticks_per_note)); i+=1; continue
                    normalized=normalize_note(raw,self.auto_low_var.get(),self.auto_high_var.get())
                    n=auto_midi(normalized,self.auto_low_var.get(),self.auto_high_var.get()) if normalized else None
                    if n is not None:
                        tie=0; j=i+1
                        while j<len(bass_values) and bass_values[j].strip()=='-':tie+=1; j+=1
                        bass_track.append(Message('note_on',note=n,velocity=80,channel=1,time=0))
                        bass_track.append(Message('note_off',note=n,velocity=0,channel=1,time=ticks_per_note*(1+tie))); i=j
                    else:
                        bass_track.append(Message('note_off',note=0,velocity=0,channel=1,time=ticks_per_note)); i+=1

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
