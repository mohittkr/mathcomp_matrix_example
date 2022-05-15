Require Import Reals Psatz.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import Rstruct.
From mathcomp Require Import mxalgebra matrix all_field.
(** The preamble above imports Reals library in Coq.
  We also import the algebra and ssrreflect library
  from mathcomp. To make the mathcomp algebra compatible
  with the real algebra from Standard Coq library, we
  import the Rstruct file from mathcomp analysis.
  Rstruct contains reflection lemmas between real
  algebra and mathcomp algebra.

  We also import mathcomp's matrix formalization:
  matrix and mxalgebra. matrix file contains definition
  of common matrices and its properties like inverse,
  diagonal matrices, triangular matrices, transpose etc.
  The mxalgebra file defines matrix algebra like 
  eigenvalues, eigenspace, matrix spaces etc.
**) 



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** We will open the real scope and the Ring scope 
  separately **)
Open Scope R_scope.
Open Scope ring_scope.

(** We instantiate the ring scope with real scope using
  Delimit Scope ... **)
Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

(** We next import the ring theory so that we can use
  it for reals **)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.



(** Define a 2 x 2 matrix: 
  [1, 2; 3, 4] **)

(** In mathcomp, matrices are defined as a function 
  over ordinal types. In this case, matrix is defines as
  a function of i and j, which is apparent from the
  if-else statement. Here, i: 'I_2, j: 'I_2 where
  'I_n is an ordinal type and denotes a finite set of
  naturals from 0.. n-1 **)
Definition A := \matrix_(i< 2, j < 2)
    (if (i == 0%N :> nat) then 
      (if (j == 0%N :> nat) then 1%Re else 2%Re) else
      (if (j == 0%N :> nat) then 3%Re else 4%Re)).

(** Check whether the element at (0,0) is 1**)
Lemma elem_at_0_0_is_1:
  A 0 0 = 1%Re.
Proof.
(** Here mxE simplies the expression A i j to extract the 
  element at i, j. i.e., mxE is a membership function.
   //= simplies trivial evaluations, which
  in this case involves evaluating if- then- else conditionals
**)
rewrite mxE //=.
Qed.

(** Define matrix transpose **)
Definition A_tr:= A^T.
(** A cool thing about mathcomp is that the math
  notations are close to Latex notations
**)


(** Proof that the trace of A is 5 **)
Lemma trace_is_5:
  \tr A = 5%Re.
Proof.
(** unfold the defintion of trace **)
rewrite /mxtrace //=.
(** Iterative sums in mathcomp are defined using the big
  operator. This is a really powerful abstraction.
  big_ord_recr expands the iterative sum as:
  \sum_(i < n.+1) F i = \sum_(i < n) F i + F n.+1
**)
(** The bang before the lemma means that we are 
  writing the lemma repeatedly
**)
rewrite !big_ord_recr //=.
(** big_ord0 means that sum of zero elements = 0 **)
rewrite big_ord0 //=.
(** add0r : 0 + r = r **)
rewrite add0r !mxE //=.
Qed.



