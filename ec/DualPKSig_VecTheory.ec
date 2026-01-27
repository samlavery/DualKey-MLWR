(* ============================================================================
   Abstract Vector Algebra Theory

   This defines the abstract interface for vector algebra that can be
   instantiated with concrete types via clone.

   Note: Some axioms (add_zero_r, neg_neg) require well-formedness/reduced
   preconditions in concrete instantiations. The unconditionally provable
   axioms are add_comm and add_assoc.
   ============================================================================ *)

require import AllCore.

(* ==========================================================================
   Abstract Vector Algebra Theory
   ========================================================================== *)

theory VecAlgebra.
  type vec.

  op zero : vec.
  op add : vec -> vec -> vec.
  op neg : vec -> vec.
  op sub (a b : vec) : vec = add a (neg b).

  (* Predicates for well-formedness - to be instantiated *)
  pred wf : vec.
  pred reduced : vec.

  (* Unconditional axioms *)
  axiom add_comm (a b : vec) : add a b = add b a.
  axiom add_assoc (a b c : vec) : add (add a b) c = add a (add b c).

  (* Conditional axioms - require well-formedness/reduced *)
  axiom add_zero_r (v : vec) : wf v => reduced v => add v zero = v.
  axiom add_neg_cancel (v : vec) : wf v => add v (neg v) = zero.
  axiom neg_neg (v : vec) : wf v => reduced v => neg (neg v) = v.

  (* Derived lemmas *)
  lemma sub_is_add_neg (a b : vec) : sub a b = add a (neg b).
  proof. by rewrite /sub. qed.

  lemma add_zero_l (v : vec) : wf v => reduced v => add zero v = v.
  proof. by move=> Hwf Hred; rewrite add_comm add_zero_r. qed.

end VecAlgebra.
