import csv
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pathlib import Path
import subprocess
import sys
import shutil
from mido import MidiFile, MidiTrack, Message, MetaMessage, bpm2tempo

TICKS_PER_BEAT = 480
BEATS_PER_BAR = 4
DEFAULT_BPM = 120
DEFAULT_BARS = 64
VISIBLE_BARS = 8
MIN_VISIBLE_BARS = 1
MAX_VISIBLE_BARS = 32

ROOTS = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B']
NOTE_TO_PC = {'C':0,'C#':1,'Db':1,'D':2,'D#':3,'Eb':3,'E':4,'F':5,'F#':6,'Gb':6,'G':7,'G#':8,'Ab':8,'A':9,'A#':10,'Bb':10,'B':11}
DEGREE_NAMES = ['Ⅰ','♭Ⅱ','Ⅱ','♭Ⅲ','Ⅲ','Ⅳ','♯Ⅳ/♭Ⅴ','Ⅴ','♭Ⅵ','Ⅵ','♭Ⅶ','Ⅶ']
CHORD_TYPES = ['', 'm', 'maj7', 'm7', '7', 'm7b5', 'dim7', 'dim', 'aug']
CHORDS = [r+t for r in ROOTS for t in CHORD_TYPES]
RESOLUTIONS = {'4分音符':1,'8分音符':2,'16分音符':4}
INTERVAL_NAMES = {0:'R',1:'m2',2:'M2',3:'m3',4:'M3',5:'P4',6:'A4/d5',7:'P5',8:'m6',9:'M6',10:'m7',11:'M7'}

class Bar:
    def __init__(self):
        self.key='C'
        self.split=False
        self.chord=''
        self.octave=3
        self.chord_1_2=''
        self.octave_1_2=3
        self.chord_3_4=''
        self.octave_3_4=3
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
        return midi_note_name(midi_from_pc_oct(pc,octv))
    n=auto_midi(s,low,high)
    return midi_note_name(n) if n is not None else s

def degree(note,key):
    note=(note or '').strip()
    key=(key or '').strip()
    if not note or note=='-':
        return ''
    pc,_=parse_note(note)
    key_pc,_=parse_note(key)
    if pc is None or key_pc is None:
        return ''
    return DEGREE_NAMES[(NOTE_TO_PC[pc]-NOTE_TO_PC[key_pc])%12]

def chord_root(chord):
    chord=(chord or '').strip()
    if not chord:
        return None
    for root in sorted(ROOTS,key=len,reverse=True):
        if chord.startswith(root):
            return root
    return None

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
    intervals={'':[0,4,7],'m':[0,3,7],'maj7':[0,4,7,11],'m7':[0,3,7,10],'7':[0,4,7,10],'m7b5':[0,3,6,10],'dim7':[0,3,6,9],'dim':[0,3,6],'aug':[0,4,8]}
    if suffix not in intervals:
        return []
    root_midi=midi_from_pc_oct(root,octv)
    return [root_midi+x for x in intervals[suffix]]

class App:
    def __init__(self,root):
        self.root=root
        self.root.title('Bass MIDI GUI PC v10')
        self.root.geometry('1500x900')
        self.root.minsize(1100,650)
        self.data=[Bar() for _ in range(DEFAULT_BARS)]
        self.page=0
        self.widgets=[]
        self.bpm_var=tk.IntVar(value=DEFAULT_BPM)
        self.bars_var=tk.IntVar(value=DEFAULT_BARS)
        self.res_var=tk.StringVar(value='4分音符')
        self.auto_low_var=tk.StringVar(value='G2')
        self.auto_high_var=tk.StringVar(value='F#3')
        self.batch_key_var=tk.StringVar(value='C')
        self.batch_chord_var=tk.StringVar(value='')
        self.midi_path=None
        self.player_process=None
        self.build_top()
        self.render()

    def build_top(self):
        top=ttk.Frame(self.root)
        top.pack(fill='x',padx=8,pady=6)
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
        ttk.Button(top,text='CSV保存',command=self.save_csv).pack(side='left',padx=(12,3))
        ttk.Button(top,text='CSV読込',command=self.load_csv).pack(side='left',padx=3)
        ttk.Button(top,text='MIDI作成',command=self.create_midi).pack(side='left',padx=3)
        ttk.Label(top,text='自動音域').pack(side='left',padx=(12,3))
        ttk.Entry(top,textvariable=self.auto_low_var,width=5).pack(side='left',padx=2)
        ttk.Label(top,text='～').pack(side='left')
        ttk.Entry(top,textvariable=self.auto_high_var,width=5).pack(side='left',padx=2)
        ttk.Label(top,text='表示8小節Key一括').pack(side='left',padx=(12,3))
        key_box=ttk.Combobox(top,textvariable=self.batch_key_var,values=ROOTS,state='readonly',width=5)
        key_box.pack(side='left',padx=2)
        ttk.Button(top,text='適用',command=self.batch_key_apply).pack(side='left',padx=2)
        ttk.Label(top,text='表示4小節コード一括').pack(side='left',padx=(12,3))
        chord_box=ttk.Combobox(top,textvariable=self.batch_chord_var,values=CHORDS,width=10)
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
        ttk.Button(nav,text='MIDI再生',command=self.play_midi).pack(side='right',padx=3)
        ttk.Button(nav,text='停止',command=self.stop_midi).pack(side='right',padx=3)

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
        self.page=min(self.page,max(0,(len(self.data)-1)//VISIBLE_BARS))
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
            self.page=(bar_no-1)//VISIBLE_BARS
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
        start=self.page*VISIBLE_BARS
        end=min(start+4,len(self.data))
        for i in range(start,end):
            self.data[i].split=False
            self.data[i].chord=chord
        self.render()

    def render(self):
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
        for pos,i in enumerate(range(start,end)):
            row=pos//4
            col=pos%4
            self.build_bar(container,i,self.data[i],row,col)

    def normalize_entry(self,var):
        raw=var.get().strip()
        if not raw or raw=='-':
            return
        normalized=normalize_note(raw,self.auto_low_var.get(),self.auto_high_var.get())
        var.set(normalized)

    def build_bar(self,parent,index,b,row,col):
        frame=ttk.LabelFrame(parent,text=f'小節 {index+1}')
        frame.grid(row=row,column=col,sticky='nw',padx=3,pady=3)
        key=tk.StringVar(value=b.key)
        split=tk.BooleanVar(value=b.split)
        chord=tk.StringVar(value=b.chord)
        c12=tk.StringVar(value=b.chord_1_2)
        c34=tk.StringVar(value=b.chord_3_4)
        chord_oct=tk.IntVar(value=b.octave)
        oct12=tk.IntVar(value=b.octave_1_2)
        oct34=tk.IntVar(value=b.octave_3_4)

        key_row=ttk.Frame(frame)
        key_row.grid(row=0,column=0,sticky='w',padx=6,pady=3)
        ttk.Label(key_row,text='Key').pack(side='left')
        key_box=ttk.Combobox(key_row,textvariable=key,values=ROOTS,state='readonly',width=5)
        key_box.pack(side='left',padx=4)

        chord_row=ttk.Frame(frame)
        chord_row.grid(row=1,column=0,sticky='w',padx=6,pady=3)
        ttk.Label(chord_row,text='Chord').pack(side='left')

        def make_chord_input(parent_row,label,var,oct_var):
            ttk.Label(parent_row,text=label).pack(side='left',padx=(8,2))
            box=ttk.Combobox(parent_row,textvariable=var,values=CHORDS,width=11)
            box.pack(side='left',padx=(0,4),ipady=3)
            ttk.Spinbox(parent_row,from_=0,to=8,textvariable=oct_var,width=4).pack(side='left',padx=(0,5),ipady=2)
            return box

        if not b.split:
            make_chord_input(chord_row,'',chord,chord_oct)
            chord_degree_label=ttk.Label(chord_row,text='',foreground='blue',width=12)
            chord_degree_label.pack(side='left',padx=8)
        else:
            make_chord_input(chord_row,'1-2拍',c12,oct12)
            make_chord_input(chord_row,'3-4拍',c34,oct34)
            chord_degree_label=ttk.Label(chord_row,text='',foreground='blue',width=18)
            chord_degree_label.pack(side='left',padx=8)

        ttk.Checkbutton(key_row,text='2拍分割',variable=split).pack(side='left',padx=8)

        bass_row=ttk.Frame(frame)
        bass_row.grid(row=2,column=0,sticky='ew',padx=6,pady=(3,6))
        ttk.Label(bass_row,text='Bass').grid(row=0,column=0,padx=(0,5),sticky='n')
        sub=RESOLUTIONS[self.res_var.get()]
        count=sub*BEATS_PER_BAR
        while len(b.bass)<count:
            b.bass.append('')
        bass=[]
        bass_key_labels=[]
        bass_chord_labels=[]

        for i in range(count):
            cell=ttk.Frame(bass_row)
            cell.grid(row=0,column=i+1,padx=2,sticky='n')
            sv=tk.StringVar(value=b.bass[i])
            ttk.Label(cell,text=f'{i/sub+1:.2g}',font=('',8)).pack()
            entry=ttk.Entry(cell,textvariable=sv,width=8)
            entry.pack(ipady=2)
            entry.bind('<Return>',lambda e,v=sv:self.normalize_entry(v))
            entry.bind('<FocusOut>',lambda e,v=sv:self.normalize_entry(v))
            entry.bind('<KeyRelease>',lambda e,v=sv:self.normalize_entry(v))
            degree_frame=ttk.Frame(cell)
            degree_frame.pack()
            dg_key=ttk.Label(degree_frame,text='',foreground='green',width=5)
            dg_key.pack(side='left')
            dg_chord=ttk.Label(degree_frame,text='',foreground='purple',width=7)
            dg_chord.pack(side='left')
            bass.append(sv)
            bass_key_labels.append(dg_key)
            bass_chord_labels.append(dg_chord)

        def current_chord(i):
            if not split.get():
                return chord.get()
            current_sub=RESOLUTIONS[self.res_var.get()]
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
            b.bass=[sv.get().strip() for sv in bass]

        def key_changed(event=None):
            apply_bar_controls()
            self.render()

        def split_changed():
            apply_bar_controls()
            self.render()

        key_box.bind('<<ComboboxSelected>>',key_changed)
        for child in key_row.winfo_children():
            if isinstance(child,ttk.Checkbutton):
                child.configure(command=split_changed)

        refresh_chord_degree()

    def last_bar(self):
        last=-1
        for i,b in enumerate(self.data):
            has_chord=bool(b.chord.strip() or b.chord_1_2.strip() or b.chord_3_4.strip())
            has_bass=any(x.strip() and x.strip()!='-' for x in b.bass)
            if has_chord or has_bass:
                last=i
        return last

    def save_csv(self):
        path=filedialog.asksaveasfilename(defaultextension='.csv',filetypes=[('CSV','*.csv')])
        if not path:
            return
        rows=[]
        for i,b in enumerate(self.data):
            rows.append([i+1,b.key,int(b.split),b.chord,b.octave,b.chord_1_2,b.octave_1_2,b.chord_3_4,b.octave_3_4]+b.bass)
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
        mid=MidiFile(ticks_per_beat=TICKS_PER_BEAT)
        bpm=int(self.bpm_var.get())
        chord_track=MidiTrack()
        mid.tracks.append(chord_track)
        chord_track.append(MetaMessage('track_name',name='Chords'))
        chord_track.append(MetaMessage('set_tempo',tempo=bpm2tempo(bpm)))
        bass_track=MidiTrack()
        mid.tracks.append(bass_track)
        bass_track.append(MetaMessage('track_name',name='Bass'))
        sub=RESOLUTIONS[self.res_var.get()]
        ticks_per_note=TICKS_PER_BEAT//sub
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

            bass_values=list(b.bass)
            while len(bass_values)<sub*4:
                bass_values.append('')
            for s in bass_values[:sub*4]:
                s=normalize_note(s,self.auto_low_var.get(),self.auto_high_var.get())
                n=auto_midi(s,self.auto_low_var.get(),self.auto_high_var.get()) if s and s!='-' else None
                if n is not None:
                    bass_track.append(Message('note_on',note=n,velocity=80,time=0))
                    bass_track.append(Message('note_off',note=n,velocity=0,time=ticks_per_note))
                else:
                    bass_track.append(Message('note_off',note=0,velocity=0,time=ticks_per_note))

        path=filedialog.asksaveasfilename(defaultextension='.mid',filetypes=[('MIDI','*.mid')])
        if not path:
            return
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
