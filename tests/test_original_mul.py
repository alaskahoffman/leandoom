"""Failure-path checks for the original-binary evidence chain, without game data."""
import hashlib
import importlib.util
import io
import pathlib
import struct
import subprocess
import tempfile
import unittest
import zipfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('original_mul', ROOT/'scripts/verify_original_mul.py')
original = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)


def image():
    """Small synthetic LE image: one code page and one internal relocation."""
    b = bytearray(0x3000)
    mz, le = 0x100, 0x180
    b[mz:mz+2] = b'MZ'
    struct.pack_into('<I', b, mz+0x3c, le-mz)
    b[le:le+4] = b'LE\0\0'
    for off, value in {8:0x10002, 0x28:4096, 0x40:0xc4, 0x44:3, 0x48:0x10c,
                       0x68:0x180, 0x6c:0x188, 0x70:0x191, 0x80:0x1000}.items():
        struct.pack_into('<I', b, le+off, value)
    struct.pack_into('<6I', b, le+0xc4, 32, 0x10000, 0x2045, 1, 1, 0)
    b[le+0x10c:le+0x110] = bytes([0,0,1,0])
    struct.pack_into('<II', b, le+0x180, 0, 9)
    struct.pack_into('<BBhBI', b, le+0x188, 7, 0x10, 20, 1, 0x12345)
    b[0x1108:0x110e] = bytes.fromhex('f7 eb 0f ac d0 10')
    return b, dict(mz_offset=hex(mz), le_offset=hex(le), code_object=1, code_size=hex(32),
                  code_flags=hex(0x2045), data_pages_offset=hex(0x1100),
                  instruction_hex='f7 eb 0f ac d0 10', site_file_offsets=['0x1108'])


class OriginalMulTests(unittest.TestCase):
    def test_page_mapping_and_nonoverlapping_relocation(self):
        b, spec = image()
        code, offsets, relocations, base = original.inspect_image(b, spec)
        self.assertEqual(base, 0x10000)
        self.assertEqual(relocations, [(20, 4)])
        self.assertEqual(original.check_sites(code, offsets, relocations, spec),
                         [(0x1108, bytes.fromhex(spec['instruction_hex']))])

    def test_relocation_into_snippet_is_rejected(self):
        b, spec = image()
        struct.pack_into('<h', b, 0x180+0x188+2, 6)  # starts before, overlaps IMUL
        code, offsets, relocations, _ = original.inspect_image(b, spec)
        with self.assertRaisesRegex(ValueError, 'relocation modifies'):
            original.check_sites(code, offsets, relocations, spec)

    def test_unsupported_fixup_and_page_formats_are_rejected(self):
        for offset, value in [(0x180+0x188, 0x27), (0x180+0x10f, 1)]:
            with self.subTest(offset=offset):
                b, spec = image()
                b[offset] = value
                with self.assertRaisesRegex(ValueError, 'unsupported'):
                    original.inspect_image(b, spec)

    def test_shift_mutation_removes_certified_site(self):
        b, spec = image()
        b[0x110d] = 15
        code, offsets, relocations, _ = original.inspect_image(b, spec)
        with self.assertRaisesRegex(ValueError, 'inventory mismatch'):
            original.check_sites(code, offsets, relocations, spec)

    def test_executable_identity_is_checked_inside_archive(self):
        inner = io.BytesIO()
        with zipfile.ZipFile(inner, 'w') as z:
            z.writestr('DOOM.EXE', b'wrong executable')
        payload = inner.getvalue()
        outer = io.BytesIO()
        with zipfile.ZipFile(outer, 'w') as z:
            z.writestr('DOOMS_19.1', payload[:20])
            z.writestr('DOOMS_19.2', payload[20:])
        with tempfile.TemporaryDirectory() as folder:
            path = pathlib.Path(folder)/'archive.zip'
            path.write_bytes(outer.getvalue())
            shareware = dict(archive_sha256=hashlib.sha256(outer.getvalue()).hexdigest())
            spec = dict(exe_member='DOOM.EXE', exe_sha256='0'*64, exe_bytes=16)
            with self.assertRaisesRegex(ValueError, 'DOOM.EXE: SHA-256 mismatch'):
                original.extract(path, shareware, spec)

    def test_kernel_certificate_rejects_changed_extracted_bytes(self):
        # Bypass Python's expected-byte comparison on purpose: the Lean certificate
        # must independently refuse to bless a different shift instruction.
        source = original.certificate([(0, bytes.fromhex('f7 eb 0f ac d0 0f'))],
                                      dict(exe_sha256='synthetic mutation'))
        with tempfile.TemporaryDirectory() as folder:
            path = pathlib.Path(folder)/'Mutant.lean'
            path.write_text(source)
            result = subprocess.run([str(ROOT/'scripts/lake'), 'env', 'lean', str(path)],
                                    cwd=ROOT, text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('false', result.stdout)

    def test_axiom_audit_rejects_additional_trust(self):
        prefix = "'Doom.Verification.Extracted."
        first = prefix+"all_extracted_bytes_match' does not depend on any axioms\n"
        for axiom in ['sorryAx', 'Lean.ofReduceBool', 'customAxiom']:
            with self.subTest(axiom=axiom), self.assertRaisesRegex(ValueError, 'trust extension'):
                original.audit_axioms(first+prefix+f"all_extracted_sites_match_engine' depends on axioms: [{axiom}]\n")
