(* Use a section to state a fact parametrized on a number n. *)

Section FactsSection.
  Variable n : nat.

  Theorem my_fact : n >= 0.
  Proof.
    apply le_0_n.
  Qed.
End FactsSection.

(* Outside the section, my_fact is universally quantified. *)

Check my_fact.
(* my_fact
     : forall n : nat, n >= 0 *)



(* Alternate approach: use a functor. *)

Module Type NAT_VALUE.
  Parameter n : nat.
End NAT_VALUE.

Module FactsFunctor(N : NAT_VALUE).
  Theorem my_fact : N.n >= 0.
  Proof.
    apply le_0_n.
  Qed.
End FactsFunctor.


(* To use the fact outside the functor, we must first instantiate the functor. *)

Module Seven.
  Definition n := 7.
End Seven.

Module FactsAboutSeven := FactsFunctor(Seven).

Check FactsAboutSeven.my_fact.
(* FactsAboutSeven.my_fact
     : Seven.n >= 0 *)