"""Lean audio parsers, C-oracle regressions, and real gameplay-to-PCM wiring."""
import hashlib,json,struct,subprocess,unittest,wave
from pathlib import Path
import audio_reference
import test_assets
from test_assets import replace
from test_combat import arena
from test_simulation import door_room
from test_wad import wad
ROOT=Path(__file__).resolve().parents[1]
PROBE=ROOT/'.lake/build/bin/audio-probe'

def mus(data):return struct.pack('<4s6H',b'MUS\x1a',len(data),16,1,0,0,0)+data

def dmx(data,rate=11025):
    data=bytes([255])*16+bytes(data)+bytes([255])*16
    return struct.pack('<HHI',3,rate,len(data))+data

def audio_lumps(silence=False):
    bank=audio_reference.corpus()[0]
    names=['pistol','shotgn','sgtatk','sgtsit','posit1','popain','dmpain','plpain','podth1','podth2','podth3','pldeth','pdiehi','slop','barexp','bgsit1','bgsit2','bgact','claw','firsht','firxpl','bgdth1','bgdth2','sgtdth','oof','noway','doropn','dorcls','bdopn','bdcls','swtchn','swtchx','pstart','pstop','stnmov','itemup','wpnup','getpow']
    sample=dmx([128]*512 if silence else ([64]*8+[192]*8)*32)
    return [('GENMIDI',bank),('D_E1M1',mus(bytes([0xb0,11,0x81,10,0x60]))),*[(('DS'+n).upper(),sample) for n in names]]

class AudioTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def probe(self,kind,data,ok=True):
        source=self.directory/'input';source.write_bytes(data)
        out=self.directory/'output'
        p=subprocess.run([str(PROBE),kind,str(source),str(out)],capture_output=True,text=True,timeout=30)
        self.assertEqual(p.returncode==0,ok,p.stderr)
        return (out.read_bytes() if ok else b''),p

    def render(self,geometry,script,assets=None):
        out=self.directory/'audio.wav'
        self.run_cli(['render-audio','E1M1',script,out],geometry+(audio_lumps() if assets is None else assets))
        with wave.open(str(out)) as w:
            self.assertEqual((w.getnchannels(),w.getsampwidth(),w.getframerate()),(2,2,44100))
            pcm=w.readframes(w.getnframes())
        return pcm,json.loads(Path(str(out)+'.json').read_text())

    def test_tables_reproduce_pinned_sources(self):
        subprocess.run(['python3',str(ROOT/'scripts/generate-audio-tables.py')],check=True,capture_output=True)

    def test_dmx_padding_rate_and_unsigned_payload(self):
        body=bytes(range(17))
        actual,p=self.probe('dmx',dmx(body,22050))
        self.assertEqual(actual,body);self.assertEqual(p.stdout.strip(),'22050')

    def test_dmx_rejects_truncation_bad_format_zero_rate_and_short_samples(self):
        valid=dmx(range(32))
        for invalid in [b'',valid[:7],valid[:-1],bytes([0])+valid[1:],valid[:2]+b'\0\0'+valid[4:],dmx(range(16))]:
            with self.subTest(length=len(invalid)):self.probe('dmx',invalid,False)

    def test_mus_velocity_percussion_time_and_controller_mapping(self):
        parsed=json.loads(self.probe('mus',audio_reference.corpus()[4])[0])
        self.assertIn([10,153,35,120],parsed['events'])
        self.assertIn([10,224,0,72],parsed['events'])
        self.assertIn([138,176,120,0],parsed['events'])
        self.assertEqual(parsed['duration'],165)

    def test_mus_rejects_invalid_or_unbounded_streams(self):
        for invalid in [b'MUS\x1a',mus(b'\x60'),mus(b'\x50'),mus(b'\x90\xbc'),mus(b'\xb0\x09\x01\x60'),mus(b'\x90\xbc\x64\xff\xff\xff\xff\xff'),mus(b'\x90\xbc\x64\x01')]:
            with self.subTest(data=invalid):self.probe('mus',invalid,False)

    def check_oracle(self,kind):
        spec=json.loads((ROOT/'tests/reference/audio.json').read_text())
        bank,events,opl,spatial,music=audio_reference.corpus()
        inp=self.directory/'commands';bankpath=self.directory/'bank';bankpath.write_bytes(bank)
        out=self.directory/'result'
        if kind=='mus':inp.write_bytes(music);args=[inp]
        else:
            commands={'driver':events,'opl':opl,'spatial':spatial,'channels':audio_reference.channel_corpus()}[kind]
            inp.write_text('\n'.join(commands)+'\n');args=[bankpath,inp] if kind=='driver' else [inp]
        subprocess.run([str(PROBE),kind,*map(str,args),str(out)],check=True,capture_output=True,timeout=30)
        data=out.read_bytes()
        if kind=='mus':data=json.dumps(json.loads(data),sort_keys=True).encode()
        self.assertEqual({'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)},spec['results'][kind])

    def test_original_music_voice_allocation_and_register_writes(self):self.check_oracle('driver')
    def test_original_mus_event_stream(self):self.check_oracle('mus')
    def test_original_stereo_attenuation(self):self.check_oracle('spatial')
    def test_original_sfx_channels_priority_and_pitch_rng(self):self.check_oracle('channels')
    def test_opl_pcm_matches_nuked(self):self.check_oracle('opl')

    def test_pistol_sound_fires_with_shot_not_windup(self):
        before,_=self.render(arena(),'4:8192')
        self.assertFalse(any(before))
        fired,trace=self.render(arena(),'5:8192')
        self.assertEqual(fired[:4*1260*4],before)
        self.assertTrue(any(fired[4*1260*4:]))
        self.assertEqual(trace['trace'][-1]['sounds'],['pistol'])

    def test_audio_pitch_preserves_gameplay_random_stream(self):
        _,audio=self.render(arena(),'19:8192')
        state=self.directory/'silent.json';self.run_cli(['combat','E1M1','19:8192',state],arena())
        silent=json.loads(state.read_text())
        self.assertEqual(audio['state']['rng'],silent['rng'])
        self.assertEqual(audio['state']['shots'],silent['shots'])
        self.assertEqual(audio['state']['miscRng'],silent['miscRng']+2)

    def test_pcm_clock_and_partition_are_exact(self):
        a,_=self.render(arena(),'30:8192')
        b,_=self.render(arena(),'5:8192,14:8192,11:8192')
        self.assertEqual(a,b);self.assertEqual(len(a),30*1260*4)

    def test_silent_pcm_and_patch_override(self):
        pcm,_=self.render(arena(),'30:8192',audio_lumps(True))
        self.assertFalse(any(pcm))
        out=self.directory/'override.wav'
        self.run_cli(['render-audio','E1M1','30:8192',out],arena()+audio_lumps(),patches=[[('DSPISTOL',dmx([128]*512))]])
        with wave.open(str(out)) as w:self.assertFalse(any(w.readframes(w.getnframes())))

    def test_door_open_and_pickup_audio(self):
        pcm,trace=self.render(door_room(),'1:4096,20:0')
        self.assertTrue(any(pcm));self.assertIn('doropn',trace['trace'][0]['sounds'])
        _,trace=self.render(arena(extras=[(0,0,0,2001,7)]),'1:2')
        self.assertIn('wpnup',trace['trace'][0]['sounds'])

    def test_imp_attack_pain_and_barrel_death_audio(self):
        _,trace=self.render(arena([(48,0,180,3001,7)]),'30:0')
        sounds=[s for t in trace['trace'] for s in t['sounds']]
        self.assertIn('bgsit1',sounds);self.assertIn('claw',sounds);self.assertIn('plpain',sounds)
        _,trace=self.render(arena([(96,0,0,2035,7)]),'50:8192')
        sounds=[s for t in trace['trace'] for s in t['sounds']]
        self.assertEqual(sounds.count('barexp'),1)

    def test_fireball_launch_and_explosion_audio(self):
        _,trace=self.render(arena([(160,0,180,3001,7)]),'145:0')
        sounds=[s for t in trace['trace'] for s in t['sounds']]
        self.assertIn('firsht',sounds);self.assertIn('firxpl',sounds)

    def test_sound_lifetime_ends_and_restart_clears_channels(self):
        pcm,_=self.render(arena(),'5:8192,10:0')
        self.assertFalse(any(pcm[-5*1260*4:]))
        pcm,_=self.render(arena(),'5:8192,1:1024,10:0')
        self.assertFalse(any(pcm[5*1260*4:]))

    def test_projectile_removal_stops_its_sound(self):
        assets=replace(audio_lumps(True),'DSFIRXPL',dmx([64]*22050))
        pcm,trace=self.render(arena([(160,0,180,3001,7)]),'170:0',assets)
        self.assertTrue(any(pcm))
        self.assertTrue(trace['state']['projectiles'][0]['removed'])
        self.assertFalse(any(pcm[-10*1260*4:]))

    def test_music_loops_and_restarts(self):
        assets=replace(audio_lumps(),'D_E1M1',mus(bytes([0x90,0xbc,100,10,0x80,60,10,0x60])))
        pcm,trace=self.render(arena(),'30:0',assets)
        self.assertTrue(any(pcm));self.assertEqual(trace['musicLoops'],5)
        initial,_=self.render(arena(),'5:0',assets)
        reset,_=self.render(arena(),'10:0,1:1024,4:0',assets)
        self.assertEqual(reset[-5*1260*4:],initial)

if __name__=='__main__':unittest.main()
