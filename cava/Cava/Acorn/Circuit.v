(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Import ListNotations MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Combinators.

(******************************************************************************)
(* Inductive to capture circuit's sequential structure                        *)
(******************************************************************************)

Section WithCava.
  Context `{semantics:Cava}.

  (* TODO: change loop here to a loop with enable *)
  (* TODO: maybe make loop have separate in/out types to reduce state info *)
  Inductive Circuit : Type -> Type -> Type :=
  | Comb : forall {i o}, (i -> cava o) -> Circuit i o
  | Compose : forall {i t o}, Circuit i t -> Circuit t o -> Circuit i o
  | First : forall {i o t}, Circuit i o -> Circuit (i * t) (o * t)
  | Second : forall {i o t}, Circuit i o -> Circuit (t * i) (t * o)
  | LoopInit :
      forall {i o : Type} {s : SignalType} (resetval : signal s),
        Circuit (i * signal s) (o * signal s) ->
        Circuit i o
  | DelayInit : forall {t} (resetval : signal t), Circuit (signal t) (signal t)
  .

  (* Loop with the default signal as its reset value *)
  Definition Loop {i o s}
    : Circuit (i * signal s) (o * signal s) -> Circuit i o :=
    LoopInit defaultSignal.
  (* Delay with the default signal as its reset value *)
  Definition Delay {t} : Circuit (signal t) (signal t) :=
    DelayInit defaultSignal.


  (* Internal state of the circuit (register values) *)
  Fixpoint circuit_state {i o} (c : Circuit i o) : Type :=
    match c with
    | Comb _ => unit
    | Compose f g => circuit_state f * circuit_state g
    | First f => circuit_state f
    | Second f => circuit_state f
    | @LoopInit i o s _ f => circuit_state f * signal s
    | @DelayInit t _ => signal t
    end.

  (* The state of the circuit after a reset *)
  Fixpoint reset_state {i o} (c : Circuit i o) : circuit_state c :=
    match c as c return circuit_state c with
    | Comb _ => tt
    | Compose f g => (reset_state f, reset_state g)
    | First f => reset_state f
    | Second f => reset_state f
    | LoopInit resetval f => (reset_state f, resetval)
    | DelayInit resetval => resetval
    end.

  (* Run circuit for a single step *)
  Fixpoint interp {i o} (c : Circuit i o)
    : circuit_state c -> i -> cava (o * circuit_state c) :=
    match c in Circuit i o return circuit_state c -> i
                                  -> cava (o * circuit_state c) with
    | Comb f => fun _ i => x <- f i ;; ret (x, tt)
    | Compose f g =>
      fun cs input =>
        '(x, cs1) <- interp f (fst cs) input ;;
        '(y, cs2) <- interp g (snd cs) x ;;
        ret (y, (cs1, cs2))
    | First f =>
      fun cs input =>
        '(x, cs') <- interp f cs (fst input) ;;
        ret (x, snd input, cs')
    | Second f =>
      fun cs input =>
        '(x, cs') <- interp f cs (snd input) ;;
        ret (fst input, x, cs')
    | LoopInit _ f =>
      fun cs input =>
        '(out, st, cs') <- interp f (fst cs) (input, snd cs) ;;
        ret (out, (cs',st))
    | DelayInit _ =>
      fun cs input =>
        ret (cs, input)
    end.
End WithCava.

Module Notations.
  Infix ">==>" := Compose (at level 40, left associativity).
End Notations.
