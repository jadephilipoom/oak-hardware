From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Arrow Require Import Category Arrow.
From Cava Require Import Arrow.ArrowExport BitArithmetic VectorUtils.

From ArrowExamples Require Import Combinators Aes.pkg Aes.naive_unrolled_cipher.

Check combinational_evaluation' unrolled_cipher_naive.
Compute (denote_kind << Bit, Vector Bit 128, Vector Bit 256, Unit >>).
Compute (combinational_evaluation' CIPH_FWD tt).

Local Notation AES data key :=
  (combinational_evaluation'
     unrolled_cipher_naive (false, (data, (key, tt)))) (only parsing).
Local Notation INV_AES data key :=
  (combinational_evaluation'
     unrolled_cipher_naive (true, (data, (key, tt)))) (only parsing).

(*
Lemma combinational_evaluation'_proper
      {CircuitLaws : CategoryLaws CircuitCat}
      i o (c c' : Circuit i o) args :
  c =M= c' ->
  combinational_evaluation' c args = combinational_evaluation' c' args.
Proof.
Qed.
 *)
Require Import Coq.Classes.Morphisms.

Context {CircuitLaws : CategoryLaws CircuitCat}
        {CircuitArrowLaws :
           ArrowLaws Kind CircuitCat CircuitLaws Unit Tuple CircuitArrow}.

About combinational_evaluation'.
About morphism_equivalence.
Locate "==>".
About respectful.
Print Relation_Definitions.relation.
Print respectful.
Definition test :
  Relation_Definitions.relation
    (forall i o : Kind, Circuit i o -> denote_kind i -> denote_kind o).
Proof.
  do 2 (eapply forall_relation; intros).
  repeat eapply @respectful.
  { exact (morphism_equivalence a a0). }
  { exact Logic.eq. }
  { exact Logic.eq. }
Defined.
Global Instance combinational_evaluation'_Proper :
  Proper  
    (forall_relation
       (fun i : Kind =>
          forall_relation
            (fun o : Kind =>
               (morphism_equivalence i o) ==> Logic.eq ==> Logic.eq)))%signature
         (@combinational_evaluation').
Admitted.

Global Instance combinational_evaluation'_naive_cipher_unrolled_Proper :
  Proper (morphism_equivalence
            (Bit ** Vector Bit 128 ** Vector Bit 256 ** Unit)
            (Vector Bit 128) ==> Logic.eq ==> Logic.eq)
         combinational_evaluation'.
Proof.
  apply combinational_evaluation'_Proper.
Qed.

Global Instance combinational_evaluation'_swap_Proper :
  Proper (morphism_equivalence
            (Bit ** Bit)
            (((Bit ** Bit) ** Unit) ** (Bit ** Bit) ** Unit)
            ==> Logic.eq ==> Logic.eq)
         combinational_evaluation'.
Proof.
  apply combinational_evaluation'_Proper.
Qed.

About compose.
Global Instance compose_Proper
       {object} {category : Category object} x y z :
  Proper ((morphism_equivalence y z) ==> (morphism_equivalence x y)
            ==> (morphism_equivalence x z))
         compose.
Admitted.

Check combinational_evaluation'_naive_cipher_unrolled_Proper.
(* bit-swap has fast rewrite *)
Goal (forall inp out k,
         @combinational_evaluation'
           (Bit ** Vector Bit (4 * 4 * 8) ** Vector Bit (8 * 4 * 8) ** Unit)
           (Vector Bit (4 * 4 * 8))
           (uncancelr >>> first swap >>> k)
           (inp) = out).
Proof.
  intros.
  rewrite (uncancelr_first_cont (category:=CircuitCat)).
Abort.

Lemma cipher_id data ekey dkey :
  INV_AES (AES data ekey) dkey = data.
Proof.
  cbn [denote_kind] in *.
  unfold unrolled_cipher_naive at 1.
  change 256 with (4 * 8 * 8).
  change 128 with (4 * 4 * 8).
  cbv [ClosureConversion.closure_conversion].
  cbn [ClosureConversion.closure_conversion'].
  (*
  change (8 * 4 * 8)%nat with 256.
  change (4 * 4 * 8)%nat with 128.
  change (4 * 4)%nat with 16.
*)
  cbn [ClosureConversion.as_kind].
  (*
  generalize CircuitArrowSTKC.
  generalize CircuitArrow.
  generalize 256.
   *)
  Set Printing Depth 1000.
  cbn [Datatypes.length].
  erewrite combinational_evaluation'_Proper.
  3:reflexivity.
  2:{
    Time
      rewrite (uncancelr_first_cont (category:=CircuitCat)).
    Search copy.
