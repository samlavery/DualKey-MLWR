(* ============================================================================
   Realized Vector Algebra - Axioms become Theorems

   This file clones the abstract VecAlgebra theory with concrete
   int list implementation, discharging all axioms with proofs.
   ============================================================================ *)

require import AllCore List IntDiv.
require VecAlgebra_Abstract VecAlgebra_Concrete.

(* Clone abstract theory, realizing axioms with concrete proofs *)
clone VecAlgebra_Abstract.VecAlgebra as RealVec with
  type vec <- int list,
  op vec_size <- VecAlgebra_Concrete.VecConcrete.vec_size,
  op vec_add <- VecAlgebra_Concrete.VecConcrete.vec_add,
  op vec_neg <- VecAlgebra_Concrete.VecConcrete.vec_neg
proof vec_add_comm by apply VecAlgebra_Concrete.VecConcrete.vec_add_comm
proof vec_neg_neg by apply VecAlgebra_Concrete.VecConcrete.vec_neg_neg
proof vec_add_assoc by apply VecAlgebra_Concrete.VecConcrete.vec_add_assoc.

(* Now RealVec.vec_add_comm, RealVec.vec_neg_neg, RealVec.vec_add_assoc
   are theorems, not axioms *)
