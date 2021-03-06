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

From Arrow Require Import Category Arrow Kappa ClosureConversion.
From Coq Require Import Lists.List NaryFunctions String Arith NArith VectorDef Lia.

Import ListNotations.
Import VectorNotations.

From Cava Require Import Types Arrow.ArrowKind.
From Cava Require Export Arrow.ArrowKind.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

(* Class CircuitLaws `(A: Arrow, ! ArrowCopy A, ! ArrowSwap A, ! ArrowDrop A) := {
  cancelr_unit_uncancelr {x}: @cancelr x >>> uncancelr =M= id;
  cancell_unit_uncancell {x}: @cancell _ _ A x >>> uncancell =M= id;
  uncancelr_cancelr {x}:      @uncancelr _ _ A x >>> cancelr =M= id;
  uncancell_cancell {x}:      @uncancell _ _ A x >>> cancell =M= id;

  drop_annhilates {x y} (f: x~>y): f >>> drop =M= drop;

  cancelr_unit_is_drop : @cancelr A unit =M= drop;
  cancell_unit_is_drop : @cancell A unit =M= drop;

  first_first   {x y z w} (f: x~>y) (g:y~>z): @first A x y w f >>> first g  =M= first (f >>> g);
  second_second {x y z w} (f: x~>y) (g:y~>z): @second A x y w f >>> second g  =M= second (f >>> g);

  swap_swap {x y}: @swap A _ x y >>> swap =M= id;

  first_id  {x w}: @first A x x w id  =M= id;
  second_id {x w}: @second A x x w id  =M= id;

  first_f  {x y w} (f: x~>y) (g:x~>y): f =M= g -> @first A x y w f =M= first g;
  second_f {x y w} (f: x~>y) (g:x~>y): f =M= g -> @second A x y w f =M= second g;
}. *)

(* Cava *)

Local Notation "[ x ~~~> .. ~~~> y ]" := (Tuple x .. (Tuple y Unit) ..).

Notation vec_index n := (Vector Bit (Nat.log2_up n)).

Inductive CircuitPrimitive :=
  | Constant (ty: Kind) (v: denote_kind ty)
  | Delay (o: Kind)
  | Not 
  | BufGate
  | Uncons (n: nat) (o: Kind)
  | Unsnoc (n: nat) (o: Kind)
  | Slice (n: nat) (x y: nat) (o: Kind) 
  | Split (n m: nat) (o: Kind) 
  | EmptyVec (o: Kind)
  | Lut (n: nat) (f: bool^^n --> bool)

  | And  
  | Nand 
  | Or   
  | Nor
  | Xor
  | Xnor 
  | Xorcy

  | Muxcy
  | UnsignedAdd (a b c: nat)
  | UnsignedSub (a: nat)
  | Index (n: nat) (o: Kind)
  | Cons (n: nat) (o: Kind)
  | Snoc (n: nat) (o: Kind)
  | Concat (n m: nat) (o: Kind).

Fixpoint primitive_input (op: CircuitPrimitive): Kind :=
  match op with
  | Constant _ _ => Unit
  | Delay o => Tuple o Unit
  | Not => Tuple Bit Unit
  | BufGate => Tuple Bit Unit
  | Uncons n o => Tuple (Vector o (S n)) Unit
  | Unsnoc n o => Tuple (Vector o (S n)) Unit
  | Slice n x y o => Tuple (Vector o n) Unit
  | Split n m o => Tuple (Vector o (n+m)) Unit
  | EmptyVec o => Unit
  | Lut n f => Tuple (Vector Bit n) Unit 

  | Muxcy => [ Bit ~~~> Tuple Bit Bit ]
  | UnsignedAdd a b c => [ Vector Bit a ~~~> Vector Bit b ]
  | UnsignedSub a => [ Vector Bit a ~~~> Vector Bit a ]
  | Index n o => [ Vector o n ~~~> vec_index n ]
  | Cons n o => [ o ~~~> Vector o n ]
  | Snoc n o => [ Vector o n ~~~> o ]
  | Concat n m o => [ Vector o n ~~~> Vector o m ]

  | _ => [ Bit ~~~> Bit ]
  end.

Fixpoint primitive_output (op: CircuitPrimitive): Kind :=
  match op with
  | Constant ty _ => ty
  | Delay o => o
  | Not => Bit
  | BufGate => Bit
  | Uncons n o => Tuple o (Vector o n)
  | Unsnoc n o => Tuple (Vector o n) o
  | Slice n x y o => Vector o (x - y + 1)
  | Split n m o => Tuple (Vector o n) (Vector o m)
  | EmptyVec o => Vector o 0
  | Lut n f => Bit

  | Muxcy => Bit
  | UnsignedAdd a b c => Vector Bit c 
  | UnsignedSub a => Vector Bit a
  | Index n o => o
  | Cons n o => Vector o (S n)
  | Snoc n o => Vector o (S n)
  | Concat n m o => Vector o (n + m)

  | _ => Bit
  end.

Notation arrow_input x := (arrow_input (object:=Kind) (unit:=Unit) (product:=Tuple) x).
Notation arrow_output x := (arrow_output (object:=Kind) (unit:=Unit) (product:=Tuple) x).

(* Single clock circuit *)
Inductive Circuit: Kind -> Kind -> Type := 
  | Structural: forall (x: ArrowStructure), Circuit (arrow_input x) (arrow_output x)
  | Primitive: forall (x: CircuitPrimitive), Circuit (primitive_input x) (primitive_output x)

  (* contains subcircuits *)
  | Composition: forall x y z, Circuit x y -> Circuit y z -> Circuit x z
  | First: forall x y z, Circuit x y -> Circuit (Tuple x z) (Tuple y z)
  | Second: forall x y z, Circuit x y -> Circuit (Tuple z x) (Tuple z y)
  | Loopr: forall x y z, Circuit (Tuple x z) (Tuple y z) -> Circuit x y
  | Loopl: forall x y z, Circuit (Tuple z x) (Tuple z y) -> Circuit x y
  .

Notation "[ x ~~> .. ~~> y ~~> z ]" := (Circuit (Tuple x .. (Tuple y Unit) ..) z) : arrow_scope.

Instance CircuitCat : Category Kind := {
  morphism X Y := Circuit X Y;
  id X := Structural (Id X);
  compose X Y Z f g := Composition X Y Z g f;
}.

Instance CircuitArrow : Arrow Kind CircuitCat Unit Tuple := {
  first  f := First f;
  second f := Second f;
  assoc   x y z := Structural (Assoc x y z);
  unassoc x y z := Structural (Unassoc x y z);
  cancelr  x := Structural (Cancelr x);
  cancell  x := Structural (Cancell x);
  uncancell x := Structural (Uncancell x);
  uncancelr x := Structural (Uncancelr x);
}.

Instance CircuitArrowDrop : ArrowDrop CircuitArrow := { drop _ := Structural (Drop _); }.
Instance CircuitArrowSwap : ArrowSwap CircuitArrow := { swap _ _ := Structural (Swap _ _); }.
Instance CircuitArrowCopy : ArrowCopy CircuitArrow := { copy _ := Structural (Copy _); }.
Instance CircuitArrowLoop : ArrowLoop CircuitArrow := { loopl := Loopl; loopr := Loopr; }.
Instance CircuitArrowSTKC : ArrowSTKC CircuitArrow := { }.

Ltac match_primitive X :=
  match X with 
  | (Circuit _ _ _) => idtac
  end.

Ltac match_compose X :=
  match X with 
  | (Composition _ _ ?Y ?Z) => idtac
  end.

Definition high : Unit ~> Bit := Primitive (Constant Bit true).
Definition low : Unit ~> Bit := Primitive (Constant Bit false).

Fixpoint insert_rightmost_tt (ty: Kind): ty ~> (insert_rightmost_unit ty).
Proof.
  intros.
  destruct ty.
  exact (second (insert_rightmost_tt ty2)).
  exact id.
  exact uncancelr.
  exact uncancelr.
Defined.

Fixpoint insert_rightmost_tt1 (ty: Kind): (remove_rightmost_unit ty) ~> ty.
Proof.
  refine (
  Fix arg_length_order_wf (fun ty => (remove_rightmost_unit ty) ~> ty )
    (fun (ty:Kind)
      (insert_rightmost_tt1': forall ty', arg_length_order ty' ty -> (remove_rightmost_unit ty') ~> ty') =>
        match ty as sty return ty=sty -> (remove_rightmost_unit sty) ~> sty with
        | Tuple _ Unit => fun _ => uncancelr
        | Tuple l ty2 => fun H => (@second _ _ _ _ _ _ _ l (insert_rightmost_tt1' ty2 _ ))
        | _ => fun _ => id
        end eq_refl
        ) ty);
  rewrite H;
  cbv [arg_length_order ty2];
  auto.
Defined.

Fixpoint remove_rightmost_tt (ty: Kind): ty ~> (remove_rightmost_unit ty).
  refine (Fix arg_length_order_wf (fun ty => ty ~> (remove_rightmost_unit ty))
    (fun (ty:Kind)
      (remove_rightmost_tt': forall ty', arg_length_order ty' ty -> ty' ~> (remove_rightmost_unit ty')) =>
        match ty as sty return ty=sty -> sty ~> (remove_rightmost_unit sty) with
        | Tuple _ Unit => fun _ => cancelr
        | Tuple l ty2 => fun H => (@second _ _ _ _ _ _ _ l (remove_rightmost_tt' ty2 _ ))
        | _ => fun _ => id
        end eq_refl
        ) ty);
  rewrite H;
  cbv [arg_length_order ty2];
  auto.
Defined.