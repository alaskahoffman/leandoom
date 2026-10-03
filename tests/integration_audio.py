"""The actual shareware E1M1 score/instruments through independent C and Lean."""
import hashlib,json,struct,subprocess,tempfile
from pathlib import Path
import audio_reference as reference
ROOT=Path(__file__).resolve().parents[1]
PROBE=ROOT/'.lake/build/bin/audio-probe'

def main():
    profile=json.loads((ROOT/'tests/reference/shareware.json').read_text())
    wad=(ROOT/profile['local_directory']/'doom1.wad').read_bytes()
    assert hashlib.sha256(wad).hexdigest()==profile['wad_sha256']
    audio=json.loads((ROOT/'tests/reference/audio.json').read_text())
    for name,sha in audio['files'].items():assert hashlib.sha256((reference.CACHE/name).read_bytes()).hexdigest()==sha,name
    n,offset=struct.unpack_from('<ii',wad,4);lumps={}
    for i in range(n):
        pos,size,name=struct.unpack_from('<ii8s',wad,offset+i*16)
        lumps[name.rstrip(b'\0').decode()]=wad[pos:pos+size]
    with tempfile.TemporaryDirectory(prefix='lean-doom-e1m1-audio-') as tmp:
        d=Path(tmp);bank=d/'bank';bank.write_bytes(lumps['GENMIDI']);score=d/'score.mus';score.write_bytes(lumps['D_E1M1'])
        for name,source in [('mus',reference.mus_source()),('driver',reference.music_driver_source()),('opl',(ROOT/'tests/reference/opl_fixture.c').read_text())]:
            c=d/(name+'.c');c.write_text(source)
            extra=['-I'+str(reference.CACHE/'opl'),str(reference.CACHE/'opl/opl3.c')] if name=='opl' else []
            subprocess.run(['cc','-std=c11','-O2','-fwrapv',*extra,str(c),'-o',str(d/name)],check=True)
        midi=d/'score.mid';parsed=d/'score.json'
        subprocess.run([str(d/'mus'),str(score),str(midi)],check=True)
        subprocess.run([str(PROBE),'mus',str(score),str(parsed)],check=True)
        expected=reference.midi_events(midi.read_bytes());assert expected==json.loads(parsed.read_text())
        events=d/'events';events.write_text('\n'.join(' '.join(map(str,e[1:])) for e in expected['events'])+'\n')
        ctrace=d/'c-registers';ltrace=d/'lean-registers'
        subprocess.run([str(d/'driver'),str(bank),str(events),str(ctrace)],check=True)
        subprocess.run([str(PROBE),'driver',str(bank),str(events),str(ltrace)],check=True)
        assert ctrace.read_bytes()==ltrace.read_bytes(),'E1M1 register trace mismatch'
        commands=[];position=0;end=44100*5
        for event,writes in zip(expected['events'],ctrace.read_text().splitlines()):
            target=event[0]*315
            if target>=end:break
            if target>position:commands.append(f's {target-position}');position=target
            commands += ['w '+entry.replace(':',' ') for entry in writes.split()]
        commands.append(f's {end-position}');input=d/'opl-input';input.write_text('\n'.join(commands)+'\n')
        cpcm=d/'c.pcm';lpcm=d/'lean.wav'
        subprocess.run([str(d/'opl'),str(input),str(cpcm)],check=True)
        subprocess.run([str(PROBE),'music',str(bank),str(score),'175',str(lpcm)],check=True)
        assert cpcm.read_bytes()==lpcm.read_bytes()[44:],'E1M1 music PCM mismatch'
        print(json.dumps({'map':'E1M1','wad_sha256':profile['wad_sha256'],'reference':audio['commit'],
          'mus_events':len(expected['events']),'duration_ticks_140hz':expected['duration'],
          'all_register_writes_match':True,'register_trace_sha256':hashlib.sha256(ctrace.read_bytes()).hexdigest(),
          'pcm_stereo_frames_compared':end,'pcm_sha256':hashlib.sha256(cpcm.read_bytes()).hexdigest(),
          'profile':'DOOM 1.9 nine-voice OPL2, immediate writes, Nuked 1.8; exact 140-Hz MUS clock. Not a DOS hardware recording.'},indent=2))

if __name__=='__main__':main()
