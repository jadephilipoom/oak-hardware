(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.MonadFacts.
Require Import Cava.BitArithmetic.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Import VectorNotations.
Close Scope vector_scope.
Import ListNotations.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.SubBytesCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance CombinationalSemantics.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma sub_bytes_fwd_bytewise:
    forall (b : byte),
    unIdent (aes_sbox_lut [false] [b]) = [byte_to_bitvec (Sbox.forward_sbox (bitvec_to_byte b))].
  Proof.
    intros.
    repeat match goal with
       | v : Vector.t _ _ |- _ => constant_vector_simpl v
    end; clear.
    repeat match goal with
       | b : bool |- _ => case b; subst b
    end; vm_compute; reflexivity.
  Qed.

  Lemma sub_bytes_inv_bytewise:
    forall (b : byte),
    unIdent (aes_sbox_lut [true] [b]) = [byte_to_bitvec (Sbox.inverse_sbox (bitvec_to_byte b))].
  Proof.
    intros.
    repeat match goal with
       | v : Vector.t _ _ |- _ => constant_vector_simpl v
    end; clear.
    repeat match goal with
       | b : bool |- _ => case b; subst b
    end; vm_compute; reflexivity.
  Qed.

  Lemma sub_bytes_bytewise is_decrypt b :
    unIdent (aes_sbox_lut [is_decrypt] [b])
    = [byte_to_bitvec
         ((if is_decrypt then Sbox.inverse_sbox else Sbox.forward_sbox)
            (bitvec_to_byte b))].
  Proof.
    destruct is_decrypt; auto using sub_bytes_fwd_bytewise, sub_bytes_inv_bytewise.
  Qed.

  Lemma opaque_byte : byte.
  Proof.
      exact (byte_to_bitvec Byte.x00).
  Qed.

  Definition state_map_no_monad (f : byte -> list byte) (st : state) : list (state) :=
    [map (map (fun b => List.hd opaque_byte (f b))) st].

  Lemma map_interchange :
    forall (st : state) (g : byte -> byte) (f : list byte -> ident (list byte)),
    (forall (b : byte), unIdent (f [b]) = [g b]) ->
    unIdent (state_map f [st]) = state_map_no_monad (fun b => unIdent (f [b])) st.
  Proof.
    intros *.
    intros hfg.
    unfold state_map_no_monad.
    unfold state_map.
    unfold column_map.

    simpl_ident.
    rewrite <- (@unpeel_singleton _ (Vec (Vec Bit 8) 4)) by congruence.
    f_equal.
    rewrite (@peel_singleton (Vec (Vec Bit 8) 4)).
    rewrite map_map.
    apply map_ext.
    intros.

    simpl_ident.
    cbn [combType].
    rewrite <- (@unpeel_singleton byte (Vec Bit 8)) by congruence.
    f_equal.
    rewrite (@peel_singleton (Vec Bit 8)).
    rewrite map_map.
    apply map_ext.
    intros.

    rewrite ! hfg.
    reflexivity.
  Qed.

  Definition sbox_raw (is_decrypt : bool) (b : byte) : byte.
    refine (_ (aes_sbox_lut [is_decrypt] [b])).
    compute.
    intros x.
    exact (List.hd opaque_byte (unIdent x)).
  Defined.

  Lemma sbox_raw_equiv :
    forall (is_decrypt : bool) (b : byte),
    unIdent (aes_sbox_lut [is_decrypt] [b]) = [sbox_raw is_decrypt b].
  Proof.
    unfold sbox_raw.
    intros.
    repeat match goal with
       | v : Vector.t _ _ |- _ => constant_vector_simpl v
    end; clear.
    repeat match goal with
       | b : bool |- _ => case b; subst b
    end; vm_compute; reflexivity.
  Qed.

  Lemma sub_bytes_equiv :
    forall (is_decrypt : bool) (st : state),
      unIdent (aes_sub_bytes [is_decrypt] [st])
    = [AES256.aes_sub_bytes_circuit_spec is_decrypt st].
  Proof.
    intros.

    cbv [aes_sub_bytes
         aes_sub_bytes_circuit_spec
         AES256.inv_sub_bytes
         AesSpec.SubBytes.inv_sub_bytes
         AES256.sub_bytes
         AesSpec.SubBytes.sub_bytes].

    cbn [seqType combType].

    rewrite (map_interchange
                st
                (sbox_raw is_decrypt)
                (@aes_sbox_lut seqType CombinationalSemantics [is_decrypt])
                (sbox_raw_equiv is_decrypt)).
    unfold state_map_no_monad.
    f_equal.

    cbv [from_flat
         to_flat
         BigEndian.to_list_rows
         BigEndian.from_list_rows].
    autorewrite with conversions.

    constant_vector_simpl st.
    repeat match goal with
       | v : t byte 4 |- _ => constant_vector_simpl v
    end; clear.

    repeat first [ progress cbn [List.map map]
                 | progress autorewrite with push_to_list push_of_list_sized ].
    rewrite ! sub_bytes_bytewise.
    destruct is_decrypt; reflexivity.
Qed.

End Equivalence.