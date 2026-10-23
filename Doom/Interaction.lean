import Doom.Engine
import HITrees.Basic

namespace Doom.Interaction
open HITrees

/-- The return of the modeled E1M1 session. A fault is an observable outcome,
not HITree.unreachable (which would erase a real obligation). -/
inductive Result where
  | exited (tic : Nat)
  | fault (message : String)
  deriving BEq, Repr

/-- `again` is a defunctionalized tail call. Its state and diagnostic events
are internal; the handler transfers to `program` rather than answering it.
No concurrency or external random-number effect is introduced. -/
inductive Request where
  | input
  | present (frame : Engine.Presentation)
  | again (state : Engine.State) (heapEvents : Array DosHeap.Event)

inductive Response where
  | command (cmd : Ticcmd)
  | acknowledged

abbrev GameE : Effect := ⟨Request, Response⟩
abbrev Tree := HITree GameE Result

def tailCall (state : Engine.State) (events : Array DosHeap.Event) : Tree :=
  .impure (.again state events) fun _ => .unreachable

def afterFrame (ctx : Engine.Context) (pending : Engine.State) : Tree :=
  match Engine.afterPresent ctx pending with
  | .error e => .pure (.fault e)
  | .ok (next, events) => tailCall next events

def onCommand (ctx : Engine.Context) (state : Engine.State) (cmd : Ticcmd) : Tree :=
  match Engine.advance ctx state cmd with
  | .error e => .pure (.fault e)
  | .ok drawn => .impure (.present drawn.presentation) fun
      | .acknowledged => afterFrame ctx drawn.pending
      | .command _ => .unreachable

/-- Finite HITree syntax for an unbounded interactive loop. `again` gives the
loop its meaning in Run below and in the live IO handler. This uses the paper's
inductive core, not a coinductive ITree or an axiom for an infinite object. -/
def program (ctx : Engine.Context) (state : Engine.State) : Tree :=
  if state.game.exitRequested then .pure (.exited state.game.ticks)
  else .impure .input fun
    | .command cmd => onCommand ctx state cmd
    | .acknowledged => .unreachable

inductive Stop where
  | waiting (tree : Tree)
  | returned (result : Result)

structure Recording where
  frames : List Engine.Presentation
  stop : Stop
  /-- Inputs after level exit/fault are not silently reported as executed. -/
  remaining : List Ticcmd

def Recording.prepend (frame : Engine.Presentation) (r : Recording) : Recording :=
  { r with frames := frame :: r.frames }

/-- Direct command-list replay through the shared engine. Records errors AFTER
presentation without losing the frame. No fixed tic bound is imposed. -/
def replay (ctx : Engine.Context) (state : Engine.State) (commands : List Ticcmd) : Recording :=
  if state.game.exitRequested then ⟨[], .returned (.exited state.game.ticks), commands⟩
  else match commands with
  | [] => ⟨[], .waiting (program ctx state), []⟩
  | cmd :: rest =>
    match Engine.advance ctx state cmd with
    | .error e => ⟨[], .returned (.fault e), rest⟩
    | .ok drawn =>
      let continuation : Recording := match Engine.afterPresent ctx drawn.pending with
        | .error e => ⟨[], .returned (.fault e), rest⟩
        | .ok (next, _) => replay ctx next rest
      continuation.prepend drawn.presentation

/-- Operational interpretation of the HITree, not an assumed equality of
recursive syntax. Input replies branch over every Ticcmd; output acknowledges
exactly one presentation. `again` unfolds without consuming input. The relation
has no global fuel limit and allows any finite prefix of an infinite playthrough. -/
inductive Run (ctx : Engine.Context) : Tree → List Ticcmd → Recording → Prop where
  | returned (result commands) :
      Run ctx (.pure result) commands ⟨[], .returned result, commands⟩
  | waiting (k) : Run ctx (.impure .input k) [] ⟨[], .waiting (.impure .input k), []⟩
  | input (k cmd commands r) : Run ctx (k (.command cmd)) commands r →
      Run ctx (.impure .input k) (cmd :: commands) r
  | present (k frame commands r) : Run ctx (k .acknowledged) commands r →
      Run ctx (.impure (.present frame) k) commands (r.prepend frame)
  | again (k state events commands r) : Run ctx (program ctx state) commands r →
      Run ctx (.impure (.again state events) k) commands r

end Doom.Interaction
