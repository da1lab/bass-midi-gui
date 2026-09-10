import csv
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pathlib import Path
import subprocess, sys, shutil
from tkinter import simpledialog
try:
    from mido import MidiFile, MidiTrack, Message, MetaMessage, bpm2tempo
except ImportError:
    raise SystemExit('mido が必要です。ターミナルで pip install mido を実行してください。')

TICKS_PER_BEAT = 480
BEATS_PER_BAR = 4
DEFAULT_BPM = 120
DEFAULT_BARS = 64
VISIBLE_BARS = 16
ROOTS = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B']
NOTE_TO_PC = {'C':0,'C#':1,'Db':1,'D':2,'D#':3,'Eb':3,'E':4,'F':5,'F#':6,'Gb':6,'G':7,'G#':8,'Ab':8,'A':9,'A#':10,'Bb':10,'B':11}
DEGREE_NAMES = ['Ⅰ','♭Ⅱ','Ⅱ','♭Ⅲ','Ⅲ','Ⅳ','♯Ⅳ/♭Ⅴ','Ⅴ','♭Ⅵ','Ⅵ','♭Ⅶ','Ⅶ']
CHORD_TYPES = ['', 'm', 'maj7', 'm7', '7', 'm7b5', 'dim7', 'dim', 'aug']
CHORDS = [r+t for r in ROOTS for t in CHORD_TYPES]
RESOLUTIONS = {'4分音符':1,'8分音符':2,'16分音符':4}

class Bar:
    def __init__(self):
        self.key='C'; self.split=False; self.chord=''; self.octave=3
        self.chord_1_2=''; self.octave_1_2=3; self.chord_3_4=''; self.octave_3_4=3
        self.bass=[]

def parse_note(s, allow_no_oct=True):
    s=(s or '').strip()
    if not s or s=='-': return None
    import re
    pat=r'^([A-Ga-g])([#b]?)(-?\d+)?$' if allow_no_oct else r'^([A-Ga-g])([#b]?)(-?\d+)$'
    m=re.match(pat,s)
    if not m: return None
    p=m.group(1).upper()+m.group(2)
    if p not in NOTE_TO_PC: return None
    return p, (int(m.group(3)) if m.group(3) is not None else None)

def midi_from_pc_oct(pc, octv): return (octv+1)*12+NOTE_TO_PC[pc]

def auto_midi(s, low='G2', high='F#3'):
    x=parse_note(s, True)
    if not x: return None
    p, octv=x
    if octv is not None: return midi_from_pc_oct(p, octv)
    lo=parse_note(low, False); hi=parse_note(high, False)
    if not lo or not hi: return None
    a=midi_from_pc_oct(*lo); b=midi_from_pc_oct(*hi)
    if a>b: return None
    for n in range(a,b+1):
        if n%12==NOTE_TO_PC[p]: return n
    return None

def midi_note_name(n): return ROOTS[n%12]+str(n//12-1)

def normalize_note(s, low='G2', high='F#3'):
    s=(s or '').strip()
    if not s or s=='-': return '-'
    x=parse_note(s, True)
    if not x: return s
    if x[1] is not None: return x[0]+str(x[1])
    n=auto_midi(s,low,high)
    return midi_note_name(n) if n is not None else s

def degree(note,key):
    x=parse_note(note,True)
    if not x or note.strip()=='-': return ''
    return DEGREE_NAMES[(NOTE_TO_PC[x[0]]-NOTE_TO_PC[key])%12]

def chord_degree(chord,key):
    if not chord: return ''
    import re
    m=re.match(r'^([A-G](?:#|b)?)(.*)$',chord)
    if not m or m.group(1) not in NOTE_TO_PC: return ''
    return DEGREE_NAMES[(NOTE_TO_PC[m.group(1)]-NOTE_TO_PC[key])%12]+m.group(2)

def chord_notes(chord, octv):
    import re
    if not chord: return []
    m=re.match(r'^([A-G](?:#|b)?)(.*)$',chord)
    if not m or m.group(1) not in NOTE_TO_PC: raise ValueError(f'不正なコードです: {chord}')
    ints={'':[0,4,7],'m':[0,3,7],'maj7':[0,4,7,11],'m7':[0,3,7,10],'7':[0,4,7,10],'m7b5':[0,3,6,10],'dim7':[0,3,6,9],'dim':[0,3,6],'aug':[0,4,8]}
    if m.group(2) not in ints: raise ValueError(f'未対応のコード種別です: {chord}')
    root=midi_from_pc_oct(m.group(1),octv)
    ns=[root+i for i in ints[m.group(2)]]
    if any(n<0 or n>127 for n in ns): raise ValueError(f'コードの音域がMIDI範囲外です: {chord}')
    return ns

class App:
    def __init__(self, root):
        self.root=root; root.title('Bass MIDI GUI PC v6'); root.geometry('1500x900'); root.minsize(1100,650)
        self.data=[Bar() for _ in range(DEFAULT_BARS)]; self.page=0; self.widgets=[]
        self.bpm=tk.IntVar(value=DEFAULT_BPM); self.bars_var=tk.IntVar(value=DEFAULT_BARS)
        self.res_var=tk.StringVar(value='4分音符'); self.repeat_var=tk.IntVar(value=0)
        self.auto_low=tk.StringVar(value='G2'); self.auto_high=tk.StringVar(value='F#3'); self.batch_key=tk.StringVar(value='C'); self.batch_chord=tk.StringVar(value='')
        self.midi_path=None; self.player_process=None
        self.build_top(); self.render()

    def build_top(self):
        top=ttk.Frame(self.root,padding=8); top.pack(fill='x')
        ttk.Label(top,text='BPM').pack(side='left'); ttk.Spinbox(top,from_=1,to=400,textvariable=self.bpm,width=6).pack(side='left',padx=(4,12))
        ttk.Label(top,text='小節数').pack(side='left'); ttk.Spinbox(top,from_=1,to=999,textvariable=self.bars_var,width=6,command=self.change_bars).pack(side='left',padx=4)
        ttk.Button(top,text='+4小節',command=lambda:self.set_bars(len(self.data)+4)).pack(side='left',padx=3)
        ttk.Button(top,text='64小節',command=lambda:self.set_bars(64)).pack(side='left',padx=3)
        ttk.Label(top,text='ベース分解能').pack(side='left',padx=(14,4)); ttk.Combobox(top,textvariable=self.res_var,values=list(RESOLUTIONS),state='readonly',width=10).pack(side='left')
        ttk.Label(top,text='先頭N小節をリピート').pack(side='left',padx=(14,4)); ttk.Spinbox(top,from_=0,to=999,textvariable=self.repeat_var,width=6).pack(side='left')
        ttk.Button(top,text='CSV保存',command=self.save_csv).pack(side='left',padx=(14,3)); ttk.Button(top,text='CSV読込',command=self.load_csv).pack(side='left',padx=3); ttk.Button(top,text='MIDI作成',command=self.make_midi).pack(side='left',padx=3)
        opt=ttk.Frame(self.root,padding=(8,0,8,6)); opt.pack(fill='x')
        ttk.Label(opt,text='自動音域').pack(side='left'); ttk.Entry(opt,textvariable=self.auto_low,width=7).pack(side='left',padx=3); ttk.Label(opt,text='〜').pack(side='left'); ttk.Entry(opt,textvariable=self.auto_high,width=7).pack(side='left',padx=3)
        ttk.Label(opt,text='（例：G2〜F#3。オクターブ省略時に使用）').pack(side='left',padx=(4,20))
        ttk.Label(opt,text='表示16小節Key一括').pack(side='left'); ttk.Combobox(opt,textvariable=self.batch_key,values=ROOTS,state='readonly',width=5).pack(side='left',padx=3); ttk.Button(opt,text='適用',command=self.batch_key_apply).pack(side='left'); ttk.Label(opt,text='表示4小節コード一括').pack(side='left',padx=(18,3)); ttk.Combobox(opt,textvariable=self.batch_chord,values=['']+CHORDS,state='readonly',width=10).pack(side='left',padx=3); ttk.Button(opt,text='適用',command=self.batch_chord_apply).pack(side='left')
        nav=ttk.Frame(self.root,padding=(8,4)); nav.pack(fill='x')
        ttk.Button(nav,text='← 前の16小節',command=lambda:self.move_page(-1)).pack(side='left'); ttk.Button(nav,text='次の16小節 →',command=lambda:self.move_page(1)).pack(side='left',padx=5)
        self.page_label=ttk.Label(nav,text=''); self.page_label.pack(side='left',padx=15)
        self.jump_var=tk.IntVar(value=1); ttk.Label(nav,text='小節へ移動').pack(side='left'); ttk.Spinbox(nav,from_=1,to=999,textvariable=self.jump_var,width=7).pack(side='left',padx=3); ttk.Button(nav,text='移動',command=self.jump).pack(side='left'); ttk.Button(nav,text='▶ MIDI再生',command=self.play_midi).pack(side='left',padx=(18,3)); ttk.Button(nav,text='■ 停止',command=self.stop_midi).pack(side='left',padx=3)

    def set_bars(self,n):
        n=max(1,int(n));
        while len(self.data)<n:self.data.append(Bar())
        if len(self.data)>n:self.data=self.data[:n]
        self.bars_var.set(n); self.page=min(self.page,max(0,(n-1)//VISIBLE_BARS)); self.render()
    def change_bars(self):
        try:self.set_bars(self.bars_var.get())
        except: pass
    def move_page(self,d): self.page=max(0,min(self.page+d,max(0,(len(self.data)-1)//VISIBLE_BARS))); self.render()
    def jump(self):
        n=max(1,min(self.jump_var.get(),len(self.data))); self.page=(n-1)//VISIBLE_BARS; self.render()
    def batch_key_apply(self):
        start=self.page*VISIBLE_BARS; end=min(start+VISIBLE_BARS,len(self.data))
        for b in self.data[start:end]: b.key=self.batch_key.get()
        self.render()

    def batch_chord_apply(self):
        start=self.page*VISIBLE_BARS; end=min(start+4,len(self.data)); chord=self.batch_chord.get()
        for b in self.data[start:end]: b.split=False; b.chord=chord
        self.render()
    def render(self):
        for w in self.widgets:w.destroy()
        self.widgets=[]
        start=self.page*VISIBLE_BARS; end=min(start+VISIBLE_BARS,len(self.data)); self.page_label.config(text=f'{start+1}〜{end} / {len(self.data)}小節')
        canvas=tk.Canvas(self.root,highlightthickness=0); sb=ttk.Scrollbar(self.root,orient='vertical',command=canvas.yview); frame=ttk.Frame(canvas)
        frame.bind('<Configure>',lambda e:canvas.configure(scrollregion=canvas.bbox('all'))); canvas.create_window((0,0),window=frame,anchor='nw'); canvas.configure(yscrollcommand=sb.set)
        canvas.pack(side='left',fill='both',expand=True,padx=(8,0)); sb.pack(side='right',fill='y'); self.widgets=[canvas,sb]
        for bi in range(start,end): self.build_bar(frame,bi)

    def build_bar(self,parent,bi):
        b=self.data[bi]; card=ttk.LabelFrame(parent,text=f'  {bi+1}小節  ',padding=5); card.pack(fill='x',pady=3,padx=2)
        row=ttk.Frame(card); row.pack(fill='x')
        ttk.Label(row,text='Key').pack(side='left'); key=tk.StringVar(value=b.key); ks=ttk.Combobox(row,textvariable=key,values=ROOTS,state='readonly',width=5); ks.pack(side='left',padx=3)
        split=tk.BooleanVar(value=b.split); ttk.Checkbutton(row,text='2拍分割',variable=split,command=lambda:self.apply_bar_controls(b,bi,key,split,chord,co,c12,oc12,c34,oc34,bass_vars)).pack(side='left',padx=8)
        ttk.Label(row,text='コード').pack(side='left')
        chord=tk.StringVar(value=b.chord); co=tk.IntVar(value=b.octave)
        c12=tk.StringVar(value=b.chord_1_2); oc12=tk.IntVar(value=b.octave_1_2); c34=tk.StringVar(value=b.chord_3_4); oc34=tk.IntVar(value=b.octave_3_4)
        self.widgets_for_bind=[]
        if b.split:
            self.code_row(row,'1-2拍',c12,oc12); self.code_row(row,'3-4拍',c34,oc34)
        else:
            self.code_row(row,'',chord,co)
        deg1=ttk.Label(row,text='',foreground='blue'); deg1.pack(side='left',padx=4)
        ttk.Label(row,text='  ベース').pack(side='left',padx=(10,2))
        bass_frame=ttk.Frame(card); bass_frame.pack(fill='x',pady=(4,0)); bass_vars=[]
        count=RESOLUTIONS[self.res_var.get()]*4
        for i in range(count):
            if i>=len(b.bass): b.bass.extend(['-']*(i+1-len(b.bass)))
            sv=tk.StringVar(value=b.bass[i]); bass_vars.append(sv)
            cell=ttk.Frame(bass_frame); cell.pack(side='left',padx=2)
            ttk.Entry(cell,textvariable=sv,width=7).pack(side='left'); dg=ttk.Label(cell,text=degree(sv.get(),b.key),foreground='green',width=5); dg.pack(side='left'); sv.trace_add('write',lambda *args,sv=sv,dg=dg,key=key: self.trace_bass(sv,dg,key))
        ttk.Button(row,text='この小節に反映',command=lambda:self.apply_bar_controls(b,bi,key,split,chord,co,c12,oc12,c34,oc34,bass_vars,normalize=True)).pack(side='right')
        self.widgets_for_bind.append((key,split,chord,co,c12,oc12,c34,oc34,bass_vars))
        ks.bind('<<ComboboxSelected>>',lambda e:self.apply_bar_controls(b,bi,key,split,chord,co,c12,oc12,c34,oc34,bass_vars))
        for var in (chord,c12,c34): var.trace_add('write',lambda *a:self.update_chord_degree(deg1,b,key,split,chord,c12,c34))
        self.update_chord_degree(deg1,b,key,split,chord,c12,c34)

    def code_row(self,parent,label,var,octvar):
        if label: ttk.Label(parent,text=label).pack(side='left',padx=(4,1))
        ttk.Combobox(parent,textvariable=var,values=['']+CHORDS,state='readonly',width=9).pack(side='left',padx=1)
        ttk.Spinbox(parent,from_=0,to=8,textvariable=octvar,width=3).pack(side='left',padx=1)
    def trace_bass(self,sv,dg,key):
        raw=sv.get(); dg.config(text=degree(raw,key.get()))
    def update_chord_degree(self,label,b,key,split,chord,c12,c34):
        if split.get(): label.config(text=f'{chord_degree(c12.get(),key.get())} / {chord_degree(c34.get(),key.get())}')
        else: label.config(text=chord_degree(chord.get(),key.get()))
    def apply_bar_controls(self,b,bi,key,split,chord,co,c12,oc12,c34,oc34,bass_vars,normalize=False):
        b.key=key.get(); b.split=split.get(); b.chord=chord.get(); b.octave=int(co.get()); b.chord_1_2=c12.get(); b.octave_1_2=int(oc12.get()); b.chord_3_4=c34.get(); b.octave_3_4=int(oc34.get())
        b.bass=[sv.get().strip() or '-' for sv in bass_vars]
        if normalize:
            b.bass=[normalize_note(x,self.auto_low.get(),self.auto_high.get()) for x in b.bass]
            self.render()
    def normalize_all(self):
        for b in self.data:b.bass=[normalize_note(x,self.auto_low.get(),self.auto_high.get()) for x in b.bass]

    def last_bar(self):
        n=0
        for i,b in enumerate(self.data):
            has_chord=(b.chord_1_2 or b.chord_3_4) if b.split else bool(b.chord)
            if has_chord or any(x!='-' for x in b.bass): n=i+1
        return n
    def play_midi(self):
        if not self.midi_path or not Path(self.midi_path).exists(): self.make_midi(); return
        self.stop_midi()
        if sys.platform=='darwin' and shutil.which('afplay'):
            self.player_process=subprocess.Popen(['afplay',self.midi_path])
        else:
            try:
                import pygame; pygame.mixer.init(); pygame.mixer.music.load(self.midi_path); pygame.mixer.music.play(); self.player_process='pygame'
            except ImportError: messagebox.showwarning('MIDI再生','MIDI再生にはmacOSのafplayまたはpygameが必要です。')
    def stop_midi(self):
        try:
            if self.player_process=='pygame':
                import pygame; pygame.mixer.music.stop()
            elif self.player_process: self.player_process.terminate()
        except Exception: pass
        self.player_process=None
    def validate_and_prepare(self):
        self.normalize_all(); end=self.last_bar()
        if not end: raise ValueError('コードまたはベースが入力されている小節がありません。')
        bpm=int(self.bpm.get());
        if bpm<=0: raise ValueError('BPMは1以上にしてください。')
        return end,bpm
    def make_midi(self):
        try:
            end,bpm=self.validate_and_prepare(); mid=MidiFile(type=1,ticks_per_beat=TICKS_PER_BEAT)
            info=MidiTrack(); info.append(MetaMessage('track_name',name='Practice Info',time=0)); info.append(MetaMessage('time_signature',numerator=4,denominator=4,clocks_per_click=24,notated_32nd_notes_per_beat=8,time=0)); info.append(MetaMessage('set_tempo',tempo=bpm2tempo(bpm),time=0)); mid.tracks.append(info)
            ct=MidiTrack(); ct.append(MetaMessage('track_name',name='Chords',time=0)); ct.append(Message('program_change',program=0,time=0));
            for b in self.data[:end]:
                parts=[(b.chord_1_2,b.octave_1_2,2),(b.chord_3_4,b.octave_3_4,2)] if b.split else [(b.chord,b.octave,4)]
                for c,o,beats in parts:
                    dur=TICKS_PER_BEAT*beats
                    if not c: ct.append(MetaMessage('marker',text='',time=dur)); continue
                    ns=chord_notes(c,o)
                    for n in ns: ct.append(Message('note_on',note=n,velocity=70,time=0))
                    for j,n in enumerate(ns): ct.append(Message('note_off',note=n,velocity=0,time=dur if j==0 else 0))
            mid.tracks.append(ct)
            bt=MidiTrack(); bt.append(MetaMessage('track_name',name='Bass - Direct Input',time=0)); bt.append(Message('program_change',program=32,time=0)); sub=RESOLUTIONS[self.res_var.get()]
            for b in self.data[:end]:
                arr=b.bass[:4*sub];
                if not arr: arr=['-']
                dur=TICKS_PER_BEAT*4//len(arr)
                for s in arr:
                    n=auto_midi(s,self.auto_low.get(),self.auto_high.get()) if s!='-' else None
                    if n is None: bt.append(MetaMessage('marker',text='',time=dur))
                    else: bt.append(Message('note_on',note=n,velocity=80,time=0)); bt.append(Message('note_off',note=n,velocity=0,time=dur))
            mid.tracks.append(bt)
            out=filedialog.asksaveasfilename(defaultextension='.mid',filetypes=[('MIDI','*.mid')],initialfile='bass_practice.mid')
            if out: mid.save(out); messagebox.showinfo('完了',f'MIDIを保存しました。\n{out}')
        except Exception as e: messagebox.showerror('MIDI作成エラー',str(e))

    def save_csv(self):
        name=simpledialog.askstring('CSVファイル名','保存するCSVファイル名を入力してください（拡張子不要）:',initialvalue='bass_midi')
        if not name:return
        name=Path(name).name
        if not name.lower().endswith('.csv'): name += '.csv'
        out=filedialog.asksaveasfilename(defaultextension='.csv',filetypes=[('CSV','*.csv')],initialfile=name)
        if not out:return
        self.normalize_all(); rows=[['bar','key','chord_split','chord','chord_octave','chord_1_2','chord_1_2_octave','chord_3_4','chord_3_4_octave','bass_resolution','bass_position','bass_note']]
        for bi,b in enumerate(self.data,1):
            for i,n in enumerate(b.bass): rows.append([bi,b.key,int(b.split),b.chord,b.octave,b.chord_1_2,b.octave_1_2,b.chord_3_4,b.octave_3_4,self.res_var.get(),i+1,n])
        with open(out,'w',newline='',encoding='utf-8-sig') as f: csv.writer(f).writerows(rows)
    def load_csv(self):
        p=filedialog.askopenfilename(filetypes=[('CSV','*.csv')]);
        if not p:return
        try:
            with open(p,'r',encoding='utf-8-sig',newline='') as f: rows=list(csv.DictReader(f))
            if not rows:return
            mp={};
            for r in rows:
                bi=int(r.get('bar','1'))-1; b=mp.setdefault(bi,Bar()); b.key=r.get('key','C') if r.get('key','C') in ROOTS else 'C'; b.split=r.get('chord_split','0')=='1'; b.chord=r.get('chord',''); b.octave=int(r.get('chord_octave') or 3); b.chord_1_2=r.get('chord_1_2',''); b.octave_1_2=int(r.get('chord_1_2_octave') or 3); b.chord_3_4=r.get('chord_3_4',''); b.octave_3_4=int(r.get('chord_3_4_octave') or 3); pos=int(r.get('bass_position','1'))-1
                while len(b.bass)<=pos:b.bass.append('-')
                b.bass[pos]=r.get('bass_note','-') or '-'
                if r.get('bass_resolution') in RESOLUTIONS:self.res_var.set(r['bass_resolution'])
            n=max(mp.keys())+1; self.data=[mp.get(i,Bar()) for i in range(n)]; self.bars_var.set(n); self.page=0; self.render()
        except Exception as e: messagebox.showerror('CSV読込エラー',str(e))

if __name__=='__main__':
    root=tk.Tk(); App(root); root.mainloop()
