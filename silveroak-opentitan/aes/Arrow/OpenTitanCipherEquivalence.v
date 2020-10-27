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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import Cava.Arrow.ArrowExport.
Require Import Cava.Arrow.CombinatorProperties.
Require Import Cava.Arrow.DeriveSpec.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import AesSpec.Cipher.
Require Import AesSpec.ExpandAllKeys.
Require Import AesSpec.InterleavedCipher.
From Aes Require Import OpenTitanCipherProperties CipherRoundProperties
     unrolled_opentitan_cipher.
Import VectorNotations.
Import ListNotations.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8) (only parsing).
  Context (sbox : pkg.SboxImpl)
          (aes_key_expand_spec :
             pkg.SboxImpl -> bool -> Vector.t bool 4 -> byte ->
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

  Notation state := (Vector.t (Vector.t (Vector.t bool 8) 4) 4) (only parsing).
  Notation key := (Vector.t (Vector.t (Vector.t bool 8) 4) 4) (only parsing).
  Notation rconst := (Vector.t bool 8) (only parsing).
  Notation keypair := (Vector.t (Vector.t (Vector.t bool 8) 4) 8) (only parsing).

  Notation nat_to_bitvec size n := (Ndigits.N2Bv_sized size (N.of_nat n)).

  (* TODO: this transpose seems odd *)
  Definition add_round_key : state -> key -> state :=
    fun st k =>
    @bitwise (Vector (Vector (Vector Bit 8) 4) 4) (fun a b => xorb a b)
             st (PkgProperties.Vector.transpose_rev k).
  Definition sub_bytes : state -> state := aes_sub_bytes_spec sbox false.
  Definition shift_rows : state -> state := aes_shift_rows_spec false.
  Definition mix_columns : state -> state := aes_mix_columns_spec false.
  Definition key_expand : nat -> rconst -> keypair -> rconst * keypair :=
    fun i => aes_key_expand_spec sbox false (nat_to_bitvec _ i).

  Definition fstkey : keypair -> key :=
    @slice_by_position
      (t (t bool 8) 4) 8 3 0 (kind_default (Vector (Vector Bit 8) 4)).
  Definition sndkey : keypair -> key :=
    @slice_by_position
      (t (t bool 8) 4) 8 7 4 (kind_default (Vector (Vector Bit 8) 4)).

  Lemma sndkey_of_append (two_keys : keypair) :
    sndkey (sndkey two_keys ++ fstkey two_keys) = fstkey two_keys.
  Proof.
    clear. cbv [fstkey sndkey slice_by_position].
    rewrite !resize_default_id.
    change (7-4+1) with 4. change (3-0+1) with 4.
    cbn [splitat fst snd Vector.append].
    autorewrite with vsimpl. reflexivity.
  Qed.

  Definition add_round_key_pair : state -> keypair -> state :=
    fun st kp => add_round_key st (sndkey kp).

  Lemma unrolled_cipher_spec_equiv
        init_keypair first_key last_key middle_keys input :
    let Nr := 14 in
    let init_rcon : Vector.t bool 8 := nat_to_bitvec _ 1 in
    (* TODO : why is the initial key pair reversed? *)
    let init_keypair_rev := sndkey init_keypair ++ fstkey init_keypair in
    let keypairs : list keypair := (first_key :: middle_keys ++ [last_key])%list in
    all_keys key_expand Nr init_keypair_rev init_rcon = keypairs ->
    unrolled_cipher_spec aes_key_expand_spec sbox false input init_keypair
    = cipher state keypair add_round_key_pair
             sub_bytes shift_rows mix_columns
             first_key last_key middle_keys input.
  Proof.
    cbv zeta. cbn [denote_kind] in *.
    intro Hall_keys.
    pose proof (hd_all_keys _ _ _ _ _ _ Hall_keys ltac:(lia)).
    subst first_key.
    erewrite <-cipher_interleaved_equiv by eassumption.
    cbv [unrolled_cipher_spec final_cipher_round_spec
                              cipher_interleaved cipher_round_interleaved].
    repeat destruct_pair_let.
    rewrite denote_kind_eqb_refl. cbn [mux].
    rewrite fold_left_fst_unchanged by auto.
    autorewrite with push_to_list.
    rewrite fold_left_map. cbn [fst snd].
    match goal with
    | |- ?LHS = ?RHS =>
      match LHS with
      | context [ @List.fold_left (?A1 * (?A2 * ?A3)) ?B1 ?f1 ?ls1 ?b1 ] =>
        match RHS with
        | context [ @List.fold_left (A1 * A3 * A2) ?B2 ?f2 ?ls2 ?b2 ] =>
          change ls1 with ls2;
            rewrite (fold_left_preserves_relation_seq
                       (fun _ x y => x = (fst (fst y), (snd y, snd (fst y))))
                       f1 f2 _ _ b1 b2)
        end
      end
    end; [ | | ].
    { (* equivalence post-loop *)
      reflexivity. }
    { (* equivalence at start of loop *)
      reflexivity. }
    { (* equivalence holds through loop body *)
      intros; subst. cbv [key_expand_and_round_spec].
      repeat destruct_pair_let; cbn [fst snd].
      rewrite denote_kind_eqb_refl. cbn [mux].
      fold fstkey sndkey. repeat (f_equal; [ ]).
      rewrite denote_kind_eqb_N2Bv_sized by (apply N_size_nat_le; cbn; Lia.lia).
      cbv [mux]. change 0%N with (N.of_nat 0).
      rewrite N.eqb_compare, N2Nat.inj_compare, !Nat2N.id, <-Nat.eqb_compare.
      reflexivity. }
  Qed.
End Equivalence.