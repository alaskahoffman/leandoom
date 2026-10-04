"""WAD-to-collision integration and explicit unsupported-domain boundaries."""
from pathlib import Path
import subprocess
import tempfile
import unittest
import fidelity_reference as reference
from test_wad import room, wad, pack

PROBE = reference.probe_for("collision_positions")
UNIT = 65536


class CollisionTests(unittest.TestCase):
    def map_query(self, lumps, x, y, radius=16*UNIT, ok=True):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "room.wad"
            path.write_bytes(wad(lumps))
            result = subprocess.run([str(PROBE), "--map-lines", str(path), "E1M1",
                                     str(x),str(y),str(radius)], text=True,capture_output=True,timeout=10)
        if ok:
            self.assertEqual(result.returncode,0,result.stderr)
            return result.stdout.strip()
        self.assertNotEqual(result.returncode,0)
        return result.stderr

    def test_decoded_map_geometry_and_tangency(self):
        # Fixture blockmap covers [-128,0); move near its west wall.
        self.assertEqual(self.map_query(room(),-48*UNIT,-32*UNIT).split()[0],"1")
        self.assertEqual(self.map_query(room(),-48*UNIT-1,-32*UNIT).split()[0],"0")
        self.assertEqual(self.map_query(room(),-32*UNIT,-32*UNIT).split()[:4],
                         ["1",str(-16*UNIT),str(128*UNIT),str(-16*UNIT)])

    def test_empty_payload_still_checks_linedef_zero(self):
        lumps = [(name,pack("hhHHHHH",-128,-128,1,1,5,0,65535) if name=="BLOCKMAP" else data)
                 for name,data in room()]
        result=self.map_query(lumps,-60*UNIT,-32*UNIT)
        self.assertEqual(result.split()[0],"0")
        self.assertTrue(result.endswith("| 1 0"),result)

    def test_unsigned_block_offset_is_explicitly_unsupported(self):
        payload=pack("hhHHH",-128,-128,1,1,32768)
        payload += bytes(32768*2-len(payload)) + pack("6H",0,0,1,2,3,65535)
        lumps=[(name,payload if name=="BLOCKMAP" else data) for name,data in room()]
        self.assertIn("outside the vanilla profile",self.map_query(lumps,-32*UNIT,-32*UNIT,ok=False))

    def test_unverified_collision_domains_are_rejected(self):
        line=f"line 0 {-32*UNIT} 0 {32*UNIT} 0 {128*UNIT} 0 {128*UNIT} 5"
        cases=[(["reset","grid -128 -128 2 2"]+[line]*9+
                ["cell 0 1 2 3 4 5 6 7 8",f"query 0 0 {16*UNIT} 0 {128*UNIT} -1 0"],
                "spechit overflow"),
               (["reset",f"thing -2147483648 0 {16*UNIT} 1","link 0 0",
                 f"query 0 0 {16*UNIT} 0 {128*UNIT} -1 0"],"abs(INT_MIN)"),
               (["reset",f"line 0 0 1 -2147483648 0 {128*UNIT} 0 0 0"],
                "slope classification")]
        for commands,message in cases:
            with self.subTest(message=message):
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    reference.run_probe(PROBE,commands)
                self.assertIn(message,error.exception.stderr)

    def test_move_rejects_corrupt_linkage(self):
        # These are safe-domain failures, not C pointer-corruption equivalence.
        setup=["reset", "grid -128 -128 2 2",
               f"line {-1000*UNIT} 0 {-1000*UNIT} {UNIT} 0 {128*UNIT} 0 0 0",
               f"world 0 {128*UNIT} 0 {128*UNIT} 0",
               f"thing 0 0 {16*UNIT} 1",f"body 0 0 {56*UNIT} 0 {128*UNIT} 4"]
        cases=[(["place 0","place 0"],"already linked"),
               (["place 0","link 3 0 0","try 0 0 0"],"inconsistent actor linkage"),
               (["try 0 0 0"],"inconsistent actor linkage")]
        for commands,message in cases:
            with self.subTest(message=message):
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    reference.run_probe(PROBE,setup+commands)
                self.assertIn(message,error.exception.stderr)

    def test_path_and_slide_reject_unverified_domains(self):
        # C intercept overruns and abs(INT_MIN) have no certified DOS profile.
        overflow=["reset","grid -256 -256 4 4"]
        overflow += [f"thing {-192*UNIT} {-160*UNIT} {16*UNIT} 1"]*3
        overflow += ["link 0 2 1 0",f"path {-240*UNIT} {-184*UNIT} {240*UNIT} {56*UNIT} 2 -1"]
        cases=[(["reset","path 1 1 -2147483647 1 0 -1"],"abs(INT_MIN)"),
               (["reset",f"line 0 0 {UNIT} {UNIT} 0 {128*UNIT} 0 0 0",
                 f"thing 0 0 {16*UNIT} 1","hit 0 0 -2147483648 1"],"abs(INT_MIN)"),
               (overflow,"intercept overflow")]
        for commands,message in cases:
            with self.subTest(message=message):
                with self.assertRaises(subprocess.CalledProcessError) as error:
                    reference.run_probe(PROBE,commands)
                self.assertIn(message,error.exception.stderr)
