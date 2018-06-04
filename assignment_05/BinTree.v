
Require Import List Omega.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Extraction Language Ocaml.

(* Extract Inductive nat => "Prelude.Int" ["0" "\x -> x + 1"] *)
(*                             "\zero succ n -> *)
(*                               if n == 0 then zero () else succ (n-1)". *)

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
    if n=0 then zero () else succ (n-1))".

Inductive bintree : Type :=
| leaf : bintree
| branch : nat -> bintree -> bintree -> bintree.


Fixpoint lookup (n:nat) (t:bintree) : Prop :=
  match t with
  | leaf => False
  | branch n' l r =>
    if eq_nat_dec n n' 
    then True
    else if le_lt_dec n n'
    then lookup n l
    else lookup n r
  end.

Fixpoint insert (x : nat) (t:bintree) : bintree :=
  match t with
  | leaf => branch x leaf leaf
  | branch y l r =>
    if le_dec x y
    then branch y (insert x l) r
    else branch y l (insert x r)
  end.

Fixpoint list2bin (l : list nat) : bintree :=
  match l with
  | [] => leaf
  | x :: xs => insert x (list2bin xs)
  end.


Fixpoint inorder (t : bintree) : list nat :=
  match t with
  | leaf => []
  | branch x l r => inorder l ++ (x :: inorder r)
  end.

Definition binsort (l : list nat) : list nat :=
  inorder (list2bin l).

Extraction "binsort_core.ml" binsort.

Example lookup_1 : lookup 1 (branch 1 leaf leaf).
Proof. reflexivity. Qed.

Example lookup_2 : lookup 2 (branch 1 leaf (branch 2 leaf leaf)).
Proof. simpl. reflexivity. Qed.

Example lookup_3 : lookup 3 (branch 4 (branch 3 leaf leaf) (branch 5 leaf leaf)).
Proof. reflexivity. Qed.

Example lookup_4 : ~ (lookup 4 (branch 1 leaf (branch 2 leaf leaf))).
Proof. unfold not. simpl. intros. assumption. Qed.

Lemma lookup_left : forall l r x n, lookup x (branch n l r) -> x < n -> lookup x l.
Proof.
  intros. unfold lookup in H.
  destruct (Nat.eq_dec x n); [omega | ].
  destruct (le_lt_dec x n); [assumption | ].
  unfold not in n0. contradiction n0. omega.
Qed.

Lemma lookup_right : forall l r x n, lookup x (branch n l r) -> n < x -> lookup x r.
Proof.
  intros. unfold lookup in H.
  destruct (Nat.eq_dec x n); [omega | ].
  destruct (le_lt_dec x n); [| assumption].
  unfold not in n0. contradiction n0. omega.
Qed.

Inductive valid : forall (t : bintree), Prop :=
| val_leaf : valid leaf
| val_cons : forall (l r : bintree) n,
    valid l -> valid r ->
    (forall x, lookup x l -> x <= n) ->
    (forall x, lookup x r -> x > n) ->
    valid (branch n l r).

Example valid_1 : valid (leaf).
Proof. apply val_leaf. Qed.

Lemma valid_end : forall x, valid (branch x leaf leaf).
Proof.
  induction x.
  - apply (val_cons _ _ 0 val_leaf val_leaf); intros; contradiction H.
  - apply (val_cons _ _ (S x) val_leaf val_leaf); intros; contradiction H.
Qed.


Lemma lookup_insert : forall t x y, valid t -> lookup x t -> lookup x (insert y t).
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction H; intros; [inversion H0 | ].
  intros. simpl in *. destruct (Nat.eq_dec x n).
  destruct (le_dec y n).
  - simpl. rewrite e. destruct (Nat.eq_dec n n); [assumption | ].
    destruct (le_lt_dec n n); omega.
  - simpl. destruct (Nat.eq_dec x n); [assumption | ].
    rewrite e. destruct (le_lt_dec n n); omega.
  - unfold not in n0. destruct (le_dec y n); simpl;
    (destruct (Nat.eq_dec x n); [apply I | ]).
    + destruct (le_lt_dec x n); [| assumption].
      apply (IHvalid1 _ _ H3).
    + destruct (le_lt_dec x n); [assumption |].
      apply (IHvalid2 _ _ H3).
Qed.

Lemma lookup_branch_x : forall l r x, lookup x (branch x l r).
Proof.
  induction l.
  - intros. simpl. destruct (Nat.eq_dec x x); [apply I |].
    destruct (le_lt_dec x x); omega.
  - intros. simpl. destruct (Nat.eq_dec x x); [apply I |].
    destruct (le_lt_dec x x); omega.
Qed.

Lemma insert_lookup_x : forall t x, valid t -> lookup x (insert x t).
Proof.
  intros. generalize dependent x. assert (H' : valid t). assumption.
  induction H; intros; simpl.
  - destruct (Nat.eq_dec x x); [apply I |].
    destruct (le_lt_dec x x); omega.
  - destruct (le_dec x n).
    + pose proof (IHvalid1 H n). destruct (insert n l); [inversion H3 |].
      simpl in *. destruct (Nat.eq_dec x n); [apply I |].
      destruct (le_lt_dec x n); [| omega].
      apply (IHvalid1 H x).
    + pose proof (IHvalid2 H0 n). destruct (insert n r); [inversion H3 |].
      simpl in *. destruct (Nat.eq_dec x n); [apply I |] .
      destruct (le_lt_dec x n); [omega |].
      apply (IHvalid2 H0 x).
Qed.

Lemma lookup_branch : forall l r x n, valid (branch n l r) ->
                                lookup x (branch n l r) ->
                                x = n \/ lookup x l \/ lookup x r.
Proof.
  intros. inversion H. unfold lookup in H0.
  destruct (Nat.eq_dec x n); [(left; assumption) |].
  destruct (le_lt_dec x n); right; [left | right]; assumption.
Qed.

Lemma insert_lookup : forall t x y,
    valid t -> x <> y -> lookup x (insert y t) -> lookup x t.
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction H; intros; simpl in *.
  - destruct (Nat.eq_dec x y); [omega |].
    destruct (le_lt_dec x y); omega.
  - destruct (Nat.eq_dec x y); [omega |]; simpl.
    destruct (Nat.eq_dec x n); [apply I |].
    destruct (le_lt_dec x n).
    + destruct (le_dec y n); simpl in H4.
      * destruct (Nat.eq_dec x n); [omega | ].
        {destruct (le_lt_dec x n); [ | omega ].
          - apply IHvalid1 with (y := y); assumption.
        }
      * destruct (Nat.eq_dec x n); [omega | ].
        destruct (le_lt_dec x n); [| omega]; assumption.
    + destruct (le_dec y n); simpl in H4.
      * destruct (Nat.eq_dec x n); [omega | ].
        destruct (le_lt_dec x n); [ omega | assumption ].
      * destruct (Nat.eq_dec x n); [omega | ].
        destruct (le_lt_dec x n); [ omega | ].
        apply IHvalid2 with (y := y). assumption. assumption.
Qed.

Lemma lookup_cases : forall t x y, valid t ->
                              lookup x (insert y t) -> x = y \/ lookup x t.
Proof.
  intros. destruct (Nat.eq_dec x y); [(left ; assumption) |].
  right. induction t.
  - simpl in *. destruct (Nat.eq_dec x y); [omega | ].
    destruct (le_lt_dec x y); assumption.
  - simpl. destruct (Nat.eq_dec x n0); [apply I | ].
    destruct (le_lt_dec x n0).
    + simpl in H0. destruct (le_dec y n0).
      * simpl in H0. destruct (Nat.eq_dec x n0); [omega |].
        destruct (le_lt_dec x n0); [ | omega].
        simpl in H. destruct (le_dec y n0); [ | omega].
        inversion H. apply (IHt1 H4 H0).
      * simpl in H0. destruct (Nat.eq_dec x n0); [omega |].
        destruct (le_lt_dec x n0); [ | omega].
        simpl in H. destruct (le_dec y n0); [ omega | assumption ].
    + simpl in H0. destruct (le_dec y n0).
      * simpl in H0. destruct (Nat.eq_dec x n0); [omega |].
        destruct (le_lt_dec x n0); [ omega | ].
        simpl in H. destruct (le_dec y n0); [ assumption | omega].
      * simpl in H0. destruct (Nat.eq_dec x n0); [omega |].
        destruct (le_lt_dec x n0); [ omega | ].
        simpl in H. destruct (le_dec y n0); [ omega | ].
        inversion H. apply (IHt2 H5 H0).
Qed.

Lemma insert_preserves : forall t x, valid t -> valid (insert x t).
Proof.
intros. induction H.
- simpl. constructor 2; (intros; try constructor; inversion H).
- simpl. destruct (le_dec x n).
  + apply val_cons; intros; [ assumption | assumption | | (apply H2; assumption)].
    destruct (lookup_cases _ _ _ H H3); [omega | ].
    apply (H1 _ H4).
  + constructor 2; intros; [assumption | assumption | (apply H1; assumption) |].
      intros. destruct (lookup_cases _ _ _ H0 H3); [omega | ].
      apply H2. assumption.
Qed.

Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - generalize dependent l'. induction l.
    + simpl. intros. right. assumption.
    + simpl. intros. destruct H; [(left; left; assumption) | ].
      rewrite or_assoc. right. apply (IHl _ H).
  - intros. generalize dependent l'. induction l.
    + simpl. intros. destruct H; [contradiction H | assumption].
    + simpl. intros. rewrite or_assoc in H.
      destruct H; [(left; assumption) |].
      right. apply (IHl _ H).
Qed.

Inductive ordered : list nat -> Prop :=
| o_nil : ordered []
| o_singleton x : ordered [x]
| o_step x y xs : x <= y -> ordered (y :: xs) -> ordered (x :: y :: xs).


Lemma ordered_app (xs ys : list nat) 
  (Hxs : ordered xs) (Hys : ordered ys) 
  (H : match (rev xs), ys with
       | x::_, y::_ => x <= y
       | _, _ => True
       end) :
  ordered (xs ++ ys).
Proof.
  induction Hxs; simpl in *; [assumption | |].
  - destruct ys; [apply o_singleton |].
    + apply (o_step x n ys H Hys).
  - apply (o_step x y (xs ++ ys) H0).
    + apply IHHxs. destruct (rev xs); simpl in *; apply H.
Qed.

Lemma lookup_in_inorder : forall t x, lookup x t -> In x (inorder t).
Proof.
  induction t; intros; simpl in *; [assumption | ].
  rewrite in_app_iff. destruct (Nat.eq_dec x n).
  - right. rewrite e. apply in_eq.
  - destruct (le_lt_dec x n).
    + left. apply IHt1. assumption.
    + right. apply in_cons. apply IHt2. assumption.
Qed.

Lemma order_cons (x:nat) (l:list nat )
  (H1: ordered l)
  (H2 : match l with
  | [] => True
  | y :: _ => x <= y
  end) : ordered (x :: l).
Proof.
  generalize dependent H2. induction H1; intros.
  - apply o_singleton.
  - apply o_step. assumption. apply o_singleton.
  - apply o_step. assumption. apply o_step. assumption. assumption.
Qed.

Lemma lookup_tree : forall t n, {lookup n t} + {~(lookup n t)}.
Proof.
  induction t; intros; simpl in *.
  - right. unfold not. intros. assumption.
  - destruct (Nat.eq_dec n0 n); [(left; apply I) |].
    destruct (le_lt_dec n0 n); [apply IHt1 | apply IHt2 ].
Qed.

Lemma cons_ordered : forall l x, ordered (x :: l) -> ordered l.
Proof.
  induction l.
  - intros. apply o_nil.
  - intros. inversion H. assumption.
Qed.

Lemma app_ordered_left : forall l1 l2, ordered (l1 ++ l2) -> ordered l1. 
Proof.
  induction l1; intros; [apply o_nil |].
  simpl in *. apply order_cons.
  - apply (IHl1 l2). inversion H; [apply o_nil | assumption].
  - destruct l1; [apply I |].
    inversion H. assumption.
Qed.  

Lemma app_sing : forall X (l1 l2 : list X) x,
   l1 ++ (x :: l2) = (l1 ++ [x]) ++ l2.
Proof.
  intros. replace (x :: l2) with ([x] ++ l2); [| reflexivity].
  rewrite app_assoc. reflexivity.
Qed.

Lemma app_ordered_right: forall l2 l1, ordered (l1 ++ l2) -> ordered l2.
Proof.
  induction l1; intros; [assumption |].
  simpl in H. pose proof (cons_ordered _ _ H). apply (IHl1 H0).
Qed.

Lemma in_inorder_lookup : forall t x, valid t ->
                                 In x (inorder t) -> lookup x t.
Proof.
  induction t; intros; simpl in *; [assumption |].
  simpl. destruct (Nat.eq_dec x n), (le_lt_dec x n); [apply I | apply I | |].
  - simpl in *. rewrite app_sing in H0.
    rewrite in_app_iff in H0. inversion H.
    apply (IHt1 _ H4).
    + destruct H0.
      * rewrite in_app_iff in H0. destruct H0; [assumption | ].
        inversion H0; [| inversion H8].
        unfold not in n0. exfalso. symmetry in H8.
        apply (n0 H8).
      * pose proof (IHt2 _ H5 H0). pose proof (H7 _ H8). omega.
  - simpl in *. inversion H. rewrite in_app_iff in H0.
    apply (IHt2 _ H5). destruct H0.
    + pose proof (IHt1 _ H4 H0). pose proof (H6 _ H8). omega.
    + inversion H0; [| assumption].
      unfold not in n0. symmetry in H8. contradiction (n0 H8).
Qed.


Lemma gt_leb : forall a b, a > b -> b <= a.
Proof.
  - intros. omega.
Qed.


Lemma inorder_valid_sorted (t : bintree) (H : valid t) : ordered (inorder t).
Proof.
  induction H; simpl; [apply o_nil |].
  apply (ordered_app _ _ IHvalid1).
  - apply (order_cons n (inorder r) IHvalid2).
    destruct (inorder r) eqn:Hr; simpl; [apply I | ].
    simpl in *. apply gt_leb. apply H2.
    apply in_inorder_lookup; [assumption |].
    rewrite Hr. constructor. reflexivity.
  - destruct (rev (inorder l)) eqn:Hr; [apply I | ].
    apply H1. apply in_inorder_lookup; [assumption |].
    assert (In n0 (n0 :: l0)); [constructor; reflexivity |].
    rewrite <- Hr in H3. rewrite <- in_rev in H3. assumption.
Qed.


Theorem list2bin_valid : forall (l : list nat), valid (list2bin l).
Proof.
  intros. induction l; [constructor |].
  simpl. apply insert_preserves. assumption.
Qed.


Theorem ordered_binsort (l : list nat) : ordered (binsort l).
Proof.
  unfold binsort. induction l; simpl; [constructor |].
  simpl. apply inorder_valid_sorted. apply insert_preserves.
  apply list2bin_valid.
Qed.

Lemma app_nil_nil : forall X (l1 l2 : list X), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  induction l1; intros; simpl in H; [| inversion H].
  split; [reflexivity | assumption].
Qed.

Lemma inorder_insert_nil_false : forall t x, inorder (insert x t) = [] -> False.
Proof.
  induction t; intros; [inversion H | ].
  simpl in H. destruct (le_dec x n).
  - inversion H. destruct (app_nil_nil _ _ _ H1); inversion H2.
  - simpl in H. destruct (app_nil_nil _ _ _ H). inversion H1.
Qed.

Lemma insert_leaf_false : forall t x, insert x t = leaf -> False.
Proof.
  induction t; intros; [inversion H | ].
  intros. simpl in H. destruct (le_dec x n); inversion H.
Qed.

Lemma binsort_perm_lr x (xs : list nat) : In x xs -> In x (binsort xs).
  generalize dependent x. induction xs; intros; [inversion H |].
  inversion H.
  - pose proof (list2bin_valid xs). rewrite H0.
    unfold binsort. simpl. apply lookup_in_inorder.
    apply insert_lookup_x. assumption.
  - unfold binsort in *. pose proof (list2bin_valid xs).
    apply lookup_in_inorder. simpl.
    apply (lookup_insert _ _ _ H1).
    apply (in_inorder_lookup _ _ H1).
    apply (IHxs _ H0).
Qed.

Lemma binsort_perm_rl x (xs : list nat) : In x (binsort xs) -> In x xs.
  generalize dependent x. unfold binsort in *. induction xs; intros; [inversion H |].
  simpl in H. destruct (Nat.eq_dec x a).
  - constructor 1. symmetry. assumption.
  - constructor 2. pose proof (list2bin_valid xs).
    apply IHxs. apply lookup_in_inorder.
    apply (insert_lookup _ _ _ H0 n).
    apply in_inorder_lookup; [| assumption].
    apply (insert_preserves _ _ H0).
Qed.

Theorem binsort_perm x (xs : list nat) : In x xs <-> In x (binsort xs).
Proof.
  split; [apply binsort_perm_lr | apply binsort_perm_rl].
Qed.




        