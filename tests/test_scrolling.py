"""Special 48 changes actual runtime sidedefs and rendered WAD textures."""
import json
import struct
import unittest
import test_assets
from test_assets import artwork,replace
from test_wad import room,pack
from test_simulation import door_room


def scroll_lines(geom,indices):
    lines=bytearray(dict(geom)['LINEDEFS'])
    for i in indices:struct.pack_into('<H',lines,i*14+6,48)
    return replace(geom,'LINEDEFS',bytes(lines))


class ScrollingTests(unittest.TestCase):
    setUp=test_assets.AssetTests.setUp
    tearDown=test_assets.AssetTests.tearDown
    run_cli=test_assets.AssetTests.run_cli

    def state(self,geom,script):
        output=self.directory/'scroll.json'
        self.run_cli(['simulate','E1M1',script,output],geom)
        return json.loads(output.read_text())

    def frame(self,geom,script):
        output=self.directory/'scroll.ppm'
        self.run_cli(['render-sim','E1M1',script,output],geom)
        return output.read_bytes()

    def test_one_unit_each_tick_and_duplicate_front_sides(self):
        for indices in ([1],[1,2],[0,1,2,3]):
            geom=scroll_lines(room(),indices)
            state=self.state(geom,'35:0')
            self.assertEqual(state['scrollers'],indices)
            self.assertEqual(state['sideOffsets'],[-8+35*len(indices)])
            self.assertEqual(state,self.state(geom,'10:0,25:0'))
            self.assertEqual(self.state(geom,'0:0'),self.state(geom,'35:0,1:1024'))

    def test_only_front_side_scrolls(self):
        geom=scroll_lines(door_room(),[2])
        self.assertEqual(self.state(geom,'35:0')['sideOffsets'],[35,0])

    def test_fixed_offset_wraps_at_signed_boundary(self):
        geom=scroll_lines(room(),[1])
        sides=bytearray(dict(geom)['SIDEDEFS']);struct.pack_into('<h',sides,0,32767)
        geom=replace(geom,'SIDEDEFS',bytes(sides))
        self.assertEqual(self.state(geom,'1:0')['sideOffsets'],[-32768])
        self.assertEqual(self.state(geom,'2:0')['sideOffsets'],[-32767])

    def test_render_uses_scrolled_offset(self):
        geom=scroll_lines(room(),[1])
        expected=bytearray(dict(geom)['SIDEDEFS']);struct.pack_into('<h',expected,0,-7)
        self.assertEqual(self.frame(artwork()+geom,'1:0'),
                         self.frame(artwork()+replace(geom,'SIDEDEFS',bytes(expected)),'0:0'))
        self.assertNotEqual(self.frame(artwork()+geom,'0:0'),self.frame(artwork()+geom,'1:0'))

    def test_scrolling_special_stops_use_before_a_door(self):
        geom=door_room()
        vertices=dict(geom)['VERTEXES']+pack('4h',32,64,32,-64)
        lines=dict(geom)['LINEDEFS']+pack('7H',6,7,4,48,0,0,1)
        geom=replace(replace(geom,'VERTEXES',vertices),'LINEDEFS',lines)
        geom=replace(geom,'BLOCKMAP',pack('hhHH6H10H',-128,-128,3,2,*([10]*6),0,*range(8),65535))
        state=self.state(geom,'1:4096,80:0')
        self.assertEqual(state['ceilings'][1],-16)
        self.assertEqual(state['doors'],[])
        self.assertIn('48',state['message'])
