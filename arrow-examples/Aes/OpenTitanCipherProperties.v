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

From Coq Require Import Derive.
From coqutil Require Import Tactics.Tactics.
From Cava Require Import Arrow.ArrowExport Arrow.DeriveSpec BitArithmetic
     Tactics VectorUtils.

From ArrowExamples Require Import CombinatorProperties PkgProperties
     CipherRoundProperties Aes.cipher_round Aes.unrolled_opentitan_cipher.

Section Wf.
  Context (aes_key_expand_Wf :
             forall sbox_impl, Wf (aes_key_expand sbox_impl))
          (aes_sub_bytes_Wf :
             forall sbox_impl, Wf (sub_bytes.aes_sub_bytes sbox_impl))
          (aes_shift_rows_Wf : Wf shift_rows.aes_shift_rows)
          (aes_mix_columns_Wf : Wf mix_columns.aes_mix_columns).

  Hint Resolve aes_key_expand_Wf aes_sub_bytes_Wf aes_shift_rows_Wf
       aes_mix_columns_Wf : Wf.

  Lemma key_expand_and_round_Wf :
    forall sbox_impl, Wf (key_expand_and_round sbox_impl).
  Proof. cbv [key_expand_and_round]; prove_Wf. Qed.
  Hint Resolve key_expand_and_round_Wf : Wf.

  Lemma unrolled_cipher_Wf :
    forall sbox_impl, Wf (unrolled_cipher sbox_impl).
  Proof. cbv [unrolled_cipher]; prove_Wf. Qed.
  Hint Resolve unrolled_cipher_Wf : Wf.

  Lemma unrolled_cipher_flat_Wf :
    forall sbox_impl, Wf (unrolled_cipher_flat sbox_impl).
  Proof. cbv [unrolled_cipher_flat]; prove_Wf. Qed.
  Hint Resolve unrolled_cipher_flat_Wf : Wf.
End Wf.
Hint Resolve key_expand_and_round_Wf unrolled_cipher_Wf unrolled_cipher_flat_Wf
     : Wf.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8) (only parsing).
  Context (aes_key_expand_spec :
             pkg.SboxImpl -> bool ->
             Vector.t bool 4 -> byte ->
             Vector.t (Vector.t byte 4) 8 ->
             byte * Vector.t (Vector.t byte 4) 8)
          (aes_key_expand_correct :
             forall sbox_impl op_i round_id rcon key_i,
               kinterp (aes_key_expand sbox_impl)
                       (op_i, (round_id, (rcon, (key_i, tt))))
               = aes_key_expand_spec sbox_impl op_i round_id rcon key_i)
          (aes_sub_bytes_correct :
             forall sbox_impl op_i state,
               kinterp (sub_bytes.aes_sub_bytes sbox_impl) (op_i, (state, tt))
               = aes_sub_bytes_spec sbox_impl op_i state)
          (aes_shift_rows_correct :
             forall op_i state,
               kinterp shift_rows.aes_shift_rows (op_i, (state, tt))
               = aes_shift_rows_spec op_i state)
           (aes_mix_columns_correct :
             forall op_i state,
               kinterp mix_columns.aes_mix_columns (op_i, (state, tt))
               = aes_mix_columns_spec op_i state).
  Hint Rewrite @aes_key_expand_correct @aes_sub_bytes_correct
       @aes_shift_rows_correct @aes_mix_columns_correct : kappa_interp.
  Opaque aes_key_expand mix_columns.aes_mix_columns.

  Derive key_expand_and_round_spec
         SuchThat (forall (sbox_impl : pkg.SboxImpl)
                     (state : bool * (byte * (Vector.t (Vector.t byte 4) 4
                                           * Vector.t (Vector.t byte 4) 8)))
                     (round : Vector.t bool 4),
                      kinterp (key_expand_and_round sbox_impl)
                              (state, (round, tt))
                      = key_expand_and_round_spec sbox_impl state round)
         As key_expand_and_round_correct.
  Proof.
    cbv [key_expand_and_round]; kappa_spec.
    repeat destruct_pair_let. cbn [fst snd].
    rewrite <-!surjective_pairing.
    derive_spec_done.
  Qed.
  Hint Rewrite @key_expand_and_round_correct : kappa_interp.
  Opaque key_expand_and_round.

  Derive unrolled_cipher_spec
         SuchThat (forall (sbox_impl : pkg.SboxImpl) (op_i : bool)
                     (data : Vector.t (Vector.t byte 4) 4)
                     (key : Vector.t (Vector.t byte 4) 8),
                      kinterp (unrolled_cipher sbox_impl)
                              (op_i, (data, (key, tt)))
                      = unrolled_cipher_spec sbox_impl op_i data key)
         As unrolled_cipher_correct.
  Proof.
    cbv [unrolled_cipher]; kappa_spec.
    repeat destruct_pair_let. cbn [fst snd].
    repeat first [derive_foldl_spec | derive_map_spec ].
    derive_spec_done.
  Qed.
  Hint Rewrite @unrolled_cipher_correct : kappa_interp.
  Opaque unrolled_cipher.

  Derive unrolled_cipher_flat_spec
         SuchThat
         (forall sbox_impl op_i (data : Vector.t bool 128) (key : Vector.t bool 256),
            kinterp (unrolled_cipher_flat sbox_impl) (op_i, (data, (key, tt)))
            = unrolled_cipher_flat_spec sbox_impl op_i data key)
         As unrolled_cipher_flat_correct.
  Proof. cbv [unrolled_cipher_flat]. derive_spec. Qed.
  Hint Rewrite @unrolled_cipher_flat_correct : kappa_interp.
  Opaque unrolled_cipher_flat.
End Equivalence.
Hint Rewrite @key_expand_and_round_correct @unrolled_cipher_correct
     @unrolled_cipher_flat_correct using solve [eauto] : kappa_interp.
Global Opaque key_expand_and_round unrolled_cipher unrolled_cipher_flat.

Require Import Coq.Lists.List.
Import ListNotations.
(* TODO: copied from spec, link this to actual spec once everything is under silveroak-opentitan *)
Notation state := (Vector.t (Vector.t (Vector.t bool 8) 4) 4) (only parsing).
Notation key := (Vector.t (Vector.t (Vector.t bool 8) 4) 4) (only parsing).
Axiom sbox : pkg.SboxImpl.
Definition add_round_key : state -> key -> state :=
  @bitwise (Vector (Vector (Vector Bit 8) 4) 4) (fun a b => xorb a b).
Definition sub_bytes : state -> state := aes_sub_bytes_spec sbox false.
Definition shift_rows : state -> state := aes_shift_rows_spec false.
Definition mix_columns : state -> state := aes_mix_columns_spec false.
Definition inv_sub_bytes : state -> state := aes_sub_bytes_spec sbox true.
Definition inv_shift_rows : state -> state := aes_shift_rows_spec true.
Definition inv_mix_columns : state -> state := aes_mix_columns_spec true.
Definition inv_mix_columns_key : key -> key := aes_mix_columns_spec true.

  Definition equivalent_inverse_cipher
             (first_key last_key : key) (middle_keys : list key)
             (input : state) : state :=
    let st := input in
    let st := add_round_key st first_key in
    let st := List.fold_left
                (fun (st : state) (round_key : key) =>
                   let st := inv_sub_bytes st in
                   let st := inv_shift_rows st in
                   let st := inv_mix_columns st in
                   let st := add_round_key st round_key in
                   st)
                middle_keys st in
    let st := inv_sub_bytes st in
    let st := inv_shift_rows st in
    let st := add_round_key st last_key in
    st.

  Definition cipher (first_key last_key : key) (middle_keys : list key)
             (input : state) : state :=
    let st := input in
    let st := add_round_key st first_key in
    let st := List.fold_left
                (fun (st : state) (round_key : key) =>
                   let st := sub_bytes st in
                   let st := shift_rows st in
                   let st := mix_columns st in
                   let st := add_round_key st round_key in
                   st)
                middle_keys st in
    let st := sub_bytes st in
    let st := shift_rows st in
    let st := add_round_key st last_key in
    st.

  Print unrolled_cipher_flat_spec.
  Notation keypair := (Vector.t (Vector.t (Vector.t bool 8) 4) 8).
  Axiom unpair : keypair -> key * key.
  About List.fold_left.
  Definition all_keys
             (key_expand : pkg.SboxImpl ->
                           bool -> Vector.t bool 4 (* round *)
                           -> Vector.t bool 8 (* rcon *)
                           -> keypair
                           -> Vector.t bool 8 * keypair)
             (nrounds : nat)
             (op_i : bool)
             (initial_rcon : Vector.t bool 8)
             (initial_key : keypair)
    : list key :=
    let result :=
        List.fold_left
          (fun '(out, rcon, round_key) round_i =>
             let round := Ndigits.N2Bv_sized 4 (BinNat.N.of_nat round_i) in
             let '(rcon, round_key) := key_expand sbox op_i round rcon round_key in
             ((out ++ [round_key])%list, rcon, round_key))
          (List.seq 0 nrounds)
          ([initial_key], initial_rcon, initial_key) in
    List.map (fun k => if op_i
                    then fst (unpair k)
                    else snd (unpair k)) (fst (fst result)).

  Lemma __ key_expand nrounds initial_keypair first_key last_key middle_keys input :
    all_keys key_expand nrounds false (Ndigits.N2Bv_sized _ (BinNat.N.of_nat 1)) initial_keypair
    = first_key :: middle_keys ++ [last_key] ->
    unrolled_cipher_flat_spec key_expand sbox false input
    = cipher first_key last_key middle_keys input.
