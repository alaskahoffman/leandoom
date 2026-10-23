# Session handoff — initialized E1M1 boundary (active scope)

## User-approved scope change

Start from explicitly corresponding initialized pinned DOS/Lean E1M1/HMP states.
Launch, DOS/filesystem, and VGA initialization verification are RETIRED from the
active critical path. Preserve the checkpoint below as historical optional work;
its “next obligations” are NOT the current task list.

Active deliverable: authentic capture/extraction where available, production
`Engine.start` output, checked initial data relation and kernel input-contract
bridge into existing aiming proofs, then preservation during admitted gameplay.
Initial capture provenance may be a stated empirical/trusted boundary; future
matching outcomes, successful aim calls, per-call readiness and preservation may
not be assumed. Choose and record a precise synchronization point: pre-wipe and
post-wipe RNG states are not interchangeable. Retain full raw state for later
render/heap/video work. No invented fixture may be called an actual DOS capture.

## Verified initialized-state slice (current)

See [INITIALIZED_E1M1_BOUNDARY.md](INITIALIZED_E1M1_BOUNDARY.md) for exact trust,
scope, commands and remaining obligations. Evidence: `artifacts/initialized-e1m1/`.

- Actual pinned DOS capture at first pre-P_Ticker CALL code+0x2081a, tick and
  leveltime zero, timedemo/nodraw/nosound. 32 MiB RAM plus 2 MiB VRAM backing
  retained, registers/segments/PC/config/commands/source hashes recorded. Not a
  restartable device save-state. Pre-wipe RNG play144/misc0, not post-wipe state.
- Production `Engine.start lumps true false` exercised, including optional heap;
  exact `state.game.player.syncScene state.game.map` aiming projection used.
- Validator checks 475 lines/portals, 828 BLOCKMAP cells with original ordering,
  92 actual mobjs and all ordered blocklinks, identity/player/flags/heights/radii,
  RNG and stamps (epoch1, all475 zero), plus authenticated relocated code ranges.
- `InitializedE1M1.started_inputs` derives actual successful Engine.start state,
  supported query profile, actual shooter lookup and four shooter-memory inputs
  from a finite checker. `fresh_pair` derives existing first/two-retry freshness
  predicates from bounded captured stamps. Generated captured-data certificate
  is kernel checked; decoding equality remains an explicit extraction boundary.
  No full aiming execution hypothesis has been renamed or assumed.
- 10 focused tests and 50 predecessor tests PASS; six strict-audited declarations;
  full proof-target build776jobs PASS; rebuilt core runtime98checks PASS. Full
  Python/game integration suite not run. RED/GREEN and negative logs retained.
- All789 old Doom source hashes unchanged; old results preserved. New files are
  opt-in capture/probe/checker/proof/tests; build/test targets and docs extended.

**Next:** formal address/pointer translation from physical capture to canonical
machine offsets; derive existing payload/list/portal and separation predicates
from checked initial data; prove transport to actual first aim entry during
admitted gameplay, ray arithmetic/capacity and then preservation. Current raw
stamp freshness is not a future-entry premise. Do not return to read/VGA/DOS
startup helpers. No full aiming, complete initial relation or game parity claim.

## Publication checkpoint — 2026-10-23 (proof work paused)

The accumulated port/proof source is being published, not a new end-to-end proof
milestone. The preceding initialized-E1M1 manifest remains frozen and historical,
not a claim that every listed file still matches its recorded hash. The interrupted
worker also left `InitializedAddress`, `InitializedScene`, `InitializedSceneRegions`,
`InitializedSceneProbe`, its verifier, tests and reference contracts. The Lean
sources/contracts remain unchanged; the two verifier/test reproducibility fixes
below are the only publication-time code changes.

- All 677 `Doom/Proofs/*.lean` targets build (786 Lake jobs). All three build
  commands from `scripts/test` also pass, including runtime and both initialized
  probes. Rebuilt `doom-tests`: 98 checks pass. Existing linter warnings remain.
- 155 selected Python tests pass: nine initialized-E1M1 tests, eight initialized
  scene tests, 29 stamp-restart/query/map proof regressions, and 109 asset,
  simulation, weapon, audio, live-comparison and original-observer tests. The
  full Python/game integration suite was not run. The actual-capture test was
  deliberately excluded: retained capture hashes/provenance were authenticated,
  not recaptured or overwritten.
- Fresh kernel certificates pass strict audits: six initialized-E1M1 declarations
  and 69 initialized-scene declarations, the latter covering 2,824 observed pointer
  slots. Positive production scene/start/layout checks and negative pointer,
  scalar, list-order, guard, certificate and audit mutations pass.
- Scene scope is typed finite incoming-memory observations and checked layout
  against a **chosen** stack envelope. It is not whole-memory/execution relocation,
  future aim-entry transport, a proof of the future ESP reserve, gameplay
  preservation, or a complete initial relation. These remain unfinished; do not
  promote this publication check into a completed initialized-gameplay milestone.
- The accumulated historical source contains 46 `bv_decide` uses in 25 files;
  those files match the frozen initialized-E1M1 source hashes. This publication
  introduced no proof changes, `sorry`, axioms, `native_decide` or `bv_decide`.
  Do not describe the entire historical tree as satisfying the newer tactic ban.

Fresh local evidence: `artifacts/publication-20261023-104440/`; inventory, scan,
build/test logs and the output-redirection harness are in
`/Users/alaska/.hermes/cache/scratch/leandoom-publication-20261023-104440/`.
The first-pass harness redirected outputs but copied the historical manifest and
pre-generated certificates, masking two clean-output defects. The follow-up below
supersedes that pass for initialized-scene reproducibility. Original top-level
initialized evidence files remain hash-checked unchanged. Captures, WADs,
executables, caches and generated evidence are intentionally not Git payloads.

### Clean-output reproducibility follow-up

- `scripts/verify_initialized_scene.py` now binds the freshly authenticated
  verifier/probe/projection inputs from `verify_files()` instead of reading the
  incidental historical `initialized-e1m1/validation.json`. Raw/canonical hashes,
  capture authentication, byte decoding and Lean checks are unchanged.
- `tests/test_initialized_scene.py` explicitly runs the verifier with `--kernel`
  in its class fixture, before any selected test. Certificate/audit mutation tests
  no longer depend on alphabetic order or an ignored certificate left on disk.
- RED: the new missing-manifest regression failed at the historical read; the
  existing certificate-mutation test selected alone failed on missing
  `CapturedPointers.lean`. GREEN: both pass in separate fresh output directories.
  No historical manifest was copied; the regression additionally blocks its read
  through a path-specific mock, without bypassing authentication.
- Final affected suites: **9 scene + 9 initialized-E1M1 tests pass** (no failures,
  errors or skips); the scene suite also passes all 9 in reverse order, with the
  strict-audit mutation test first. The standalone certificate-negative test passes
  after generating its own valid fixture. The actual-capture test remains excluded
  to avoid overwriting the retained capture; full integration was not rerun.
- Fresh production scene/start/layout checks pass; strict kernel audits still
  cover 69 scene declarations / 2,824 observed pointer slots and six E1M1
  declarations. This is not a whole-project strict audit or a new proof milestone.
- Rechecking the frozen historical manifest finds eight differing entries
  (including this handoff, retained capture/evidence, `lakefile.lean` and
  `scripts/test`), but no differing `Doom/` entries. Do not regenerate that
  manifest or describe its complete hash inventory as current. The retained
  capture passes its own current provenance and pinned-byte authentication.

Follow-up evidence: `artifacts/publication-20261023-104440/reprofix/validation.json`.
RED/GREEN logs and the fresh-directory harness: the scratch path above plus
`reprofix/` (`validate.py`, `red-manifest.log`, `green-manifest.log`,
`red-certificate.log`, `green-certificate.log`, `scene-suite.log`,
`scene-reversed.log`, `boundary-suite.log`). The harness generates the production
projection afresh and only links the retained authenticated capture. Run it with
an unused label and optional test method names to keep prior evidence intact.
Only the verifier, scene tests and this handoff are changed/staged by this fix;
no runtime/proof source changes, commit or push.

## Frozen historical checkpoint — 2026-10-21

## Goal, authorization and preserved boundary

Faithful Lean DOOM from original execution to an aiming-relevant initialized
state related to production `Engine.start`. **Startup is NOT complete.**
Repo `/Users/alaska/Documents/chatgpt/lean` resolves to canonical `ChatGPT/lean`.
Continue automatically, normal approvals, one writer, no nested coding agents.
Huge dirty tree: never reset/clean/stash/discard/commit. No new sorry/axiom/
native_decide/bv_decide; strict allowlist propext, Quot.sound, Classical.choice.
Use `./scripts/lake`, scratch TMPDIR, Python recursion10000 and bounded batches.
No ancestor AGENTS.md exists. No runtime/interpreter/predecessor Doom edits.

Pins: EXE b8020523561a5ad9706e009a52d61c578f37faafd85ac471962308406292ce27;
WAD 1d7d43be501e67d927e415e0b8f3e29c3bf33075e859721816f652a526cac771.
Python extraction/mapping/relocation/hash binding remains a trust boundary.
Separate code/data memory, total flat data memory: no fetch/access-fault,
segmentation, VGA hardware or DOS interrupt refinement has been proved.

## New verified original-entry frontier

Three opt-in modules, preserving all old contracts:

1. `E1M1AimReadPrologue.entry_execution`: same original0x2e3e0 through both real
   allocations, zeroing, cache MISS, actual W_ReadLump CALL and its15-instruction
   prologue. Executes five PUSHes, EDI9/EBPraw, signed count guard, directory
   ECX=180+table, real I_BeginRead CALL0x38c26→0x1adb0. Bound5419;
   ESP=originalESP-80, actual return0x38c2b. No supplied reached directory.
2. `E1M1AimDiskRead.entry_execution`: actual I_BeginRead three PUSHes,
   CMP[0x29134],0 and JE. Branch is selected from the preserved ORIGINAL flag.
   - Nonzero: reaches active hardware arm0x1adc0, ESP=originalESP-92.
   - Zero: executes all three POPs and RET to0x38c2b, ESP=originalESP-76.
   Bound5428 covers both. All non-ESP registers are preserved by this bounded
   icon interval; EDI9, EBPraw and ECX180+table remain derived. Zero is NOT
   asserted as the reached startup configuration. No active-icon return assumed.
3. `E1M1AimReadRequest.entry_execution`: explicitly conditional on ORIGINAL
   [0x29134]=0, extends the real icon return through actual directory-handle
   branch and file CALL, total≤5436 instructions.
   - Original [table+188]=-1: pushes mode0x200 and original filename pointer
     [0x74f9c], CALL0x38c3f→0x40691; ESP=originalESP-88, return0x38c44.
   - Otherwise: ESI=handle, EAX=handle, EDX=original[table+192], EBX0;
     CALL0x38c6b→0x408c0; ESP=originalESP-80, return0x38c70.
   Does NOT execute either wrapper or imply an OS-valid handle/successful seek.
   It never chooses the existing-handle branch for convenience.

Exact seams: `E1M1AimReadPrologue.entered s h table cache`,
`E1M1AimDiskRead.boundary s h table cache`,
`E1M1AimReadRequest.boundary s h table cache`. Preserve these names before
rewrites; do not unfold the2916-store memory during composition.

## New initial conditions and frames

- `E1M1AimReadPrologue.OriginalSafe`: original-address prior allocation/fill/cache
  separation plus previous raw-allocation/read-CALL addresses. `read_frame`
  transports ORIGINAL input words, not fabricated reached memory.
- Prologue `Conditions` protects directory count0x74fa0 and pointer0x74fa4;
  new stack addresses are originalESP-60/-64/-68/-72/-76/-80. Kernel regression
  exhibits that old guards through-72 do NOT protect-76.
- Disk `Conditions` protects original[0x29134] through the same old writes,
  read prologue and newly used originalESP-84/-88/-92. No successful helper
  execution is a field of these conditions.
- File `Conditions` protects original directory handle/offset and filename
  pointer through prior writes, prologue and icon saves. `namePush` separately
  protects [0x74f9c] from the mode PUSH at originalESP-80.
- Exact ordered write-list memory equalities, arbitrary protected-word frames
  and byte frames are proved. The prologue explicitly preserves all11664 side
  zero bytes; disk and request byte-frame lemmas carry those or arbitrary raw
  bytes through their real stack writes. Produced metadata/count/upper words
  can be transported from the preceding produced-memory frame; never equate
  produced count648 with an unconstrained original count cell.
- I_BeginRead saved-word restoration and its caller RET word follow from
  three actual PUSHes and pairwise slot separation, including wrapping stacks.
- Raw19440 payload remains UNLOADED. No loaded image or W_ReadLump success is
  an assumption/conclusion. The independent CPU confirms every raw byte stayed
  unchanged throughout these intervals.

## Important discovered scope boundary — do NOT bypass active VGA

Authenticated reconnaissance `next-boundaries.json` finds an earlier real
MOV EBX,1 at0x1a021 and store[0x29134],EBX at0x1a041. Their reached execution is
not yet proved, but they make treating zero as the actual video history unsafe.
The new theorem retains BOTH flag outcomes. The zero-only file-request result
is a conditional component, not pinned startup reachability.

Nonzero I_BeginRead next formal frontier is0x1adc0, before MOV EDX0x3c4 /
MOV AL2 / OUT DX,AL at0x1adc7. Subsequent VGA sequencer/graphics-controller
OUTs, IN AL,DX at0x1addf from0x3cf, and aperture copies involve read-mode/latches
and planar memory. The ordinary flat-byte model has NOT been refined to them.
This is genuine hardware modeling work, not a successful-helper premise to add.
A scoped device-state/I/O transition interface (with justified frames), or an
actual proof of a supported disabled-video history, is required. Do not silently
select disabled icon to make the miss complete. Parent may continue deterministic
wrapper work in parallel conceptually, but use only the single implementation writer.

## Exact next obligations

1. Active icon0x1adc0: opt-in exact byte-immediate/port/device semantics and VGA
   memory effects, or an explicitly justified observational/device abstraction.
   Preserve actual EAX clobbers, saved regs and both copy loops; no generic RET.
2. Conditional existing-handle seek starts0x408c0; actual INT21/AH42 is0x408d9.
   Prelude uses MOV BX,CX, MOV AH42, SHR ECX16. Add exact opt-in partial-register
   semantics/flags, derive deeper frames; then explicit DOS/file resource state.
   Post-INT writes SS:[EDI] AX/DX and RCL/ROR move CF into sign before error test.
3. Reopen starts0x40691, calls0x406b0; actual INT21/AH3D is0x406e0. Needs filename
   bytes, descriptor history, exact stack arguments and real error paths. Mode
   passed is0x200. No assumed open success or supplied descriptor table.
4. Read0x40935 first CALL0x4289d at0x40943. Handle metadata reads bound[0x1f7ac]
   and vector[0x1f800]; small handles can CALL0x427f8. Binary flag0x40 path uses
   INT21/AH3F0x40985; text path INT0x409b9 filters CR/0x1a and can loop. Model
   actual resource/position/input transitions, not arbitrary loaded payload.
5. W_ReadLump compares return count with signed JGE at0x38c81 (NOT equality).
   Optional close0x40902 INT21/AH3E0x4090b; I_EndRead0x1aea0 also active VGA.
   Five POPs/RET0x38caa, cache return0x38d50→0x2e445, then gate0x2e445..0x2e46a
   and Incoming/UpperStack join to existing648-body loop remain unproved.
6. Tag1 HIT remains at prior genuinely conditional original-cell/signature
   `tagRequested`0x399b0. Not advanced here. Actual CMP/JL/store/POP/RET→0x38cd3
   and cache epilogue remain useful alternate components, never pinned history.

Earlier heap restrictions remain: first split derives free remainder; first
no-split requires ORIGINAL free-successor words/history. Additional raw capacity
rounded19440=19464≤nextView.size is explicit and not implied by first capacity.
Both first and second split/no-split execute. Raw split leaves a FREE immediate
neighbor: occupied-next cleanup needs real occupancy or actual coalescing proof.
Detailed preceding contracts remain in `artifacts/e1m1-aim-cache-heap/` and
this checkpoint's frozen `handoff-before.md`.

Later actual R_InitTextures/catalog order, vertex/sector/linedef/blockmap,
actor identities/list order/RNG/filter/light/layout and production Engine.start
relation remain. allocateOnly/forget are not payload proofs. Startup requires
one continuous original-boundary execution establishing actual related contents,
tables and stamps; dynamic play/whole-game parity are separate.

## Final-source validation

Evidence `artifacts/e1m1-aim-read-prologue/`:
-39 new public contracts,3866 strict audit entries/3848 distinct declarations.
 Cumulative certificate92 authenticated ranges (90 inherited+read187bytes and
 I_BeginRead240bytes). Full bytes are bound; unsupported active instructions
 are NOT thereby claimed executed. Old interpreters unchanged/fail closed.
-107 distinct tests PASS:10 focused,16 cache,27 memset,19 connected,35 allocator.
 Negative prologue/icon/CALL bytes, file/code mappings, relocation, six missing
 guards including disabled condition, strict-audit mutations, new-slot and
 unsupported OUT/INT kernel checks. RED/GREEN logs retained.
- Full proof-target build from actual `scripts/test`:775jobs PASS, no new proof
 warnings. Separate Lean replay+strict audit PASS. Runtime/game suite NOT run.
-1152 uninterrupted independent CPU original-entry fixtures:384 active icon,
 384 zero-icon existing handle,384 zero-icon reopen; all first/second allocation
 branches,8 heads,4 tails, wrapping/unaligned stacks. All registers, ordered
 writes, complete mapped data, zero output, unchanged raw payload, owner/header,
 count/base, upper stack and defined flags checked. No PC/register patching or
 mocked helper returns/interrupts. These are constructed placements, not earlier
 DOS startup history. Category subtotals overlap except the three modes.
-826-file preturn baseline frozen. All784 old Doom sources and39 prior evidence
 files unchanged; only intentional scripts/test and handoff/plan edits allowed.
-`validation.json` binds final sources/docs/evidence and baseline preservation.
 No owned Lean probes remain; no commits, resets or runtime-source edits.

## Reproduction

```sh
export TMPDIR=/Users/alaska/.hermes/cache/scratch
./scripts/lake build Doom.Proofs.E1M1AimReadRequest
PYTHONPATH=scripts:tests python3 -m unittest test_e1m1_aim_read_prologue -v
.tools/x86-check/bin/python scripts/verify_e1m1_aim_read_prologue.py --cross-check
./scripts/lake env lean artifacts/e1m1-aim-read-prologue/Checked.lean > "$TMPDIR/read-audit.log"
PYTHONPATH=scripts python3 -c 'from pathlib import Path; import os; from verify_e1m1_aim_read_prologue import audit; audit((Path(os.environ["TMPDIR"])/"read-audit.log").read_text())'
PYTHONPATH=scripts .tools/x86-check/bin/python artifacts/e1m1-aim-read-prologue/recon-next.py
```

Resolved proof pitfall: expose exact `boundary` on the LHS BEFORE rewriting an
original branch value. Rewriting inside unfolded result first changes the seam,
then defeq may unfold the entire zero loop trying to recover it. Use simp-only
BitVec arithmetic on already named register equalities, not broad simplification.
Continue automatically; this is a verified partial read checkpoint, NOT full
read/cache return or initialized startup.
