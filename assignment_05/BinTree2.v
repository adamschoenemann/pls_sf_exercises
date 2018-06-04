Require Import List Omega.
Import ListNotations.

Inductive bintree : Type := 
| leaf : bintree
| node : nat -> bintree -> bintree -> bintree.

Fixpoint lookup (n : nat) (t : bintree) : Prop :=
    match t with
    | leaf => False 
    | node x l r => if eq_nat_dec x n
                    then True 
                    else if le_lt_dec n x
                    then lookup n l
                    else lookup n r
    end.

Inductive valid : bintree -> Type :=
| val_leaf : valid leaf
| val_node : forall x l r, valid l -> valid r ->
                      (forall y, lookup y l -> y <= x)  ->
                      (forall y, lookup y r -> y > x) -> 
                      valid (node x l r).

Fixpoint insert (x : nat) (t : bintree) : bintree :=
    match t with
    | leaf => node x leaf leaf
    | node y l r => if le_lt_dec x y
                    then node y (insert x l) r
                    else node y l (insert x r)
    end.

Fixpoint inorder (t : bintree) : list nat :=
    match t with
    | leaf => []
    | node x l r => inorder l ++ (x :: inorder r)
    end.

Fixpoint list_to_bin (xs : list nat) : bintree :=
    match xs with
    | [] => leaf
    | x :: xs' => insert x (list_to_bin xs')
    end.

Definition binsort (xs : list nat) : list nat := inorder (list_to_bin xs).

Example binsort_ex_01 : binsort [10;4;3;6;2;3;0;0;1] = [0;0;1;2;3;3;4;6;10].
Proof. reflexivity. Qed.

Inductive ordered : list nat -> Type :=
| o_nil  : ordered []
| o_sing : forall x, ordered [x]
| o_cons : forall x y xs, x <= y -> ordered (y :: xs) -> ordered (x :: y :: xs).

Lemma lookup_leaf_false (x : nat) : lookup x leaf -> False.
Proof.
  intros. inversion H.
Qed.

Lemma lookup_insert (t : bintree) (x y : nat) :
  lookup y (insert x t) -> y = x \/ lookup y t.
Proof.
  induction t; intros; simpl in *.
  - destruct (Nat.eq_dec x y).
    + left. symmetry. assumption.
    + right. destruct (le_lt_dec y x); assumption.
  - destruct (le_lt_dec x n); simpl in *; destruct (Nat.eq_dec n y);
        try (right; constructor); destruct (le_lt_dec y n).
    + apply (IHt1 H).
    + right. assumption.
    + right. assumption.
    + apply (IHt2 H).
  Qed.

Lemma insert_valid (x : nat) (t : bintree) : valid t -> valid (insert x t).
Proof.
  intros. generalize dependent x. induction t; intros; simpl in *.
  - constructor; intros; try constructor; contradiction (lookup_leaf_false y H0).
  - inversion H. subst. destruct (le_lt_dec x n).
    + apply (val_node _ _ _ (IHt1 H3 x) H4); intros.
      * destruct (lookup_insert t1 x y H0); 
                [subst; assumption | apply (H5 _ H1)].
      * apply (H6 _ H0).
    + apply (val_node _ _ _ H3 (IHt2 H4 x) H5).
      intros. destruct (lookup_insert t2 x y H0).
      * subst. omega.
      * apply (H6 _ H1).
Qed.

Lemma list_to_bin_valid (xs : list nat) : valid (list_to_bin xs).
Proof.
    induction xs; simpl; [constructor |].
    apply (insert_valid _ _ IHxs).
Qed.

Lemma ordered_app (xs ys : list nat) (y : nat) : 
  ordered xs -> ordered (y :: ys) -> (forall x, In x xs -> x <= y) ->
  ordered (xs ++ y :: ys).
Proof.
  induction xs; intros; simpl in *; [assumption |].
  inversion H; subst; simpl in *.
  - constructor.
    + apply H1. left. reflexivity.
    + assumption.
  - constructor.
    + assumption.
    + apply (IHxs H5 H0). intros. destruct H2; simpl in *.
      * subst. apply H1. right. left. reflexivity.
      * apply H1. right. right. assumption.
Qed.

Lemma ordered_cons (xs : list nat) :
  forall (x : nat), (forall z, In z xs -> x <= z) -> ordered xs -> ordered (x :: xs).
Proof.
  induction xs; intros; simpl in *; constructor.
  - apply H. left. reflexivity.
  - apply (IHxs a). intros.
    + inversion H0; subst. inversion H1. 
      apply le_trans with (m := y). assumption. 
      simpl in *. destruct H1.
      * omega.
      * more stuff


  
Lemma inorder_valid_ordered (t : bintree) : valid t -> ordered (inorder t).
Proof.
  intros H. induction H; [constructor |].
  simpl in *. apply (ordered_app _ _ _ IHvalid1).
  - 

Theorem ordered_binsort (xs : list nat) : ordered (binsort xs).
Proof. 
  unfold binsort. simpl. intros.
Theorem binsort_perm x (xs : list nat) : In x xs <-> In x (binsort xs).


