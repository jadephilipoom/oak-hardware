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

Require Import Coq.Classes.Morphisms.

Global Instance combinational_evaluation'_Proper
       {circuit_laws : CategoryLaws CircuitCat} :
  Proper  
    (forall_relation
       (fun i : Kind =>
          forall_relation
            (fun o : Kind =>
               (morphism_equivalence i o)
                 ==> Logic.eq ==> Logic.eq)))%signature
         (@combinational_evaluation').
Admitted.

Global Instance combinational_evaluation'_naive_cipher_unrolled_Proper
       {circuit_laws : CategoryLaws CircuitCat} :
  Proper (morphism_equivalence
            (Bit ** Vector Bit 128 ** Vector Bit 256 ** Unit)
            (Vector Bit 128) ==> Logic.eq ==> Logic.eq)
         combinational_evaluation'.
Proof. apply combinational_evaluation'_Proper. Qed.

Global Instance compose_Proper
       {object} {category : Category object}
       {category_laws : CategoryLaws category}
       x y z :
  Proper ((morphism_equivalence y z) ==> (morphism_equivalence x y)
            ==> (morphism_equivalence x z))
         compose.
Admitted.

(* TODO: add something to categorylaws *)
Global Instance first_Proper
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {x y z : object} :
  Proper ((morphism_equivalence x y)
            ==> (morphism_equivalence (x ** z) (y ** z)))
         first.
Admitted.

(* TODO: add something to categorylaws *)
Global Instance second_Proper
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {x y z : object} :
  Proper ((morphism_equivalence x y)
            ==> (morphism_equivalence (z ** x) (z ** y)))
         second.
Admitted.

Context {CircuitLaws : CategoryLaws CircuitCat}
        {CircuitArrowLaws :
           ArrowLaws Kind CircuitCat CircuitLaws Unit Tuple CircuitArrow}.

Goal (forall (f : Unit ~[CircuitCat]~> Unit)
             (k : Unit ** Unit ~[_]~> Unit ** Unit)
             m,
         morphism_equivalence
           <<Unit ** Unit>> <<(Unit ** Unit) ** Unit>>
           (first (uncancell >>> second f >>> k))
           (first m)).
Proof.
  intros.
  rewrite uncancell_second_cont.
Abort.

Lemma first_first_cont
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {v w x y z} (f : x ~> y) (g : y ~> z) (k : z ** w ~> v):
  first f >>> first g >>> k =M= first (f >>> g) >>> k.
Admitted.

Lemma swap_swap
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {x y}:
  swap >>> swap =M= (id (x:=x **y)).
Admitted.

Lemma first_id_cont
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {x y z} (k : x ** y ~> z):
  first id >>> k =M= k.
Admitted.

Lemma unassoc_assoc_cont
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {w x y z} (k : x ** y ** z ~> w) :
  unassoc >>> assoc >>> k =M= k.
Admitted.

Lemma second_second_cont
       {object category unit product}
       {arrow : Arrow object category unit product}
       {arrow_laws : CategoryLaws arrow}
       {v w x y z} (f : x ~> y) (g : y ~> z) (k : w ** z ~> v):
  second f >>> second g >>> k =M= second (f >>> g) >>> k.
Admitted.

Print fold_right.
Eval cbn [List.fold_right List.seq] in (List.fold_right Nat.add 0 (List.seq 0 4)).
Eval cbn [List.fold_left List.seq] in (List.fold_left Nat.add (List.seq 0 4) 0).
Axiom xor_spec : list bool -> list bool -> list bool.
Axiom sub_bytes_spec : list bool -> list bool.
Axiom shift_rows_spec : list bool -> list bool.
Axiom mix_columns_spec : list bool -> list bool.
Axiom key_expand_spec : list bool -> list bool.
Definition cipher_round_spec (data key : list bool) : list bool :=
  let data := xor_spec data key in
  let data := sub_bytes_spec data in
  let data := shift_rows_spec data in
  let data := mix_columns_spec data in
  data.
Definition aes_cipher_spec
           (nrounds : nat)
           (data key : list bool) : list bool :=
  (* first xor *)
  let data := xor_spec data key in
  let key := key_expand_spec key in
  (* main loop *)
  let st :=
      List.fold_left (fun st _ =>
                        let data := fst st in
                        let key := snd st in
                        (cipher_round_spec data key, key_expand_spec key))
                     (List.seq 0 nrounds) (data, key) in
  let data := fst st in
  let key := snd st in
  (* final cipher round *)
  let data := xor_spec data key in
  let data := sub_bytes_spec data in
  let data := shift_rows_spec data in
  data.

About unrolled_cipher_naive.
Search t list.
Lemma unrolled_cipher_naive_equiv n data key :
  to_list (AES data key) = aes_cipher_spec n (to_list data) (to_list key).
Proof.
  cbn [denote_kind] in *.
  unfold unrolled_cipher_naive.
  change 256 with (4 * 8 * 8).
  change 128 with (4 * 4 * 8).
  rewrite expression_evaluation_is_arrow_evaluation.
  cbn [interp_combinational].
  Print reshape.
  (* What is needed to prove the id lemma with kappa/arrows?
     What is needed to prove the id lemma with monads?
     What about the equivalence?
     experiment with all 4?
 *)
     
  Set Printing Implicit.

Lemma cipher_id data ekey dkey : INV_AES (AES data ekey) dkey = data.
Proof.
  cbn [denote_kind] in *.
  unfold unrolled_cipher_naive at 1 2.
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
    Hint Rewrite
         @first_cancelr_cont
         @second_cancell_cont
         @uncancelr_first_cont
         @uncancell_second_cont using solve [typeclasses eauto]
    : arrowlaws.
    Time
      autorewrite with arrowlaws.
    repeat match goal with
           | |- context [first (?a >>> ?b)] =>
             let f := fresh "f" in
             set (f:=(a >>> b))
           | |- context [second (?a >>> ?b)] =>
             let f := fresh "f" in
             set (f:=(a >>> b))
           end.
    rewrite first_first_cont.
    rewrite swap_swap.
    rewrite first_id_cont.
    rewrite unassoc_assoc_cont.
    rewrite second_second_cont.
    (*
      input :
      << Bit ** (Vector Bit (4 * 4 * 8)
         ** (Vector Bit (4 * 8 * 8) ** Unit >>
                    (op_i, (data, (key, tt)))
  swap >>>          ((data, (key, tt)), op_i)
  uncancelr >>>     (((data, (key, tt)), op_i), tt)
  assoc >>>         ((data, (key, tt)), (op_i, tt))
  first swap >>>    (((key, tt), data), (op_i, tt))
  assoc >>>         ((key, tt), (data, (op_i, tt)))
  first swap >>>    ((tt, key), (data, (op_i, tt)))
  assoc >>>         (tt, (key, (data, (op_i, tt))))
  second
    (copy >>>
     first f0) >>>  (tt, (f0 (key, (data, (op_i, tt)))),
                             (key, (data, (op_i, tt))))
  second
    (copy >>>
     first f) >>>   (tt, (f (f0 kdou, kdou), (f0 kdou, kdou))
  unassoc >>>       ((tt, f (f0 kdou, kdou)), (f0 kdou, kdou))
  first swap >>>    ((f (f0 kdou, kdou), tt), (f0 kdou, kdou))
  second drop >>>   ((f (f0 kdou, kdou), tt), tt)
  cancelr >>>       (f (f0 kdou, kdou), tt)
  flatten
     *)
    
    
    rewrite cancelr_flatten.
    .
