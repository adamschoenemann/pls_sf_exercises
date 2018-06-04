
Definition admit {T: Type} : T.  Admitted.

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
  end.

Compute (next_weekday monday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
    Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.


Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false=> b2
  end.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb: false || false || true = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31:                 (andb3 true true true) = true.
  Proof. simpl. reflexivity.  Qed. (* FILL IN HERE *) 
Example test_andb32:                 (andb3 false true true) = false.
  Proof. simpl. reflexivity. Qed.    (* FILL IN HERE *) 
Example test_andb33:                 (andb3 true false true) = false.
  Proof. simpl. reflexivity. Qed.      (* FILL IN HERE *) 
Example test_andb34:                 (andb3 true true false) = false.
  Proof. simpl. reflexivity. Qed.   (* FILL IN HERE *) 


Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
    | O => m
    | S k => S (plus k m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n,m with
    | O, _ => O
    | S _, O => S n
    | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => 1
    | S k => mult base (exp base k)
  end.


Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n,m with
    | O, O => true
    | S n', O => false
    | O, S m' => false
    | S n', S m' => beq_nat n' m'
  end.

Fixpoint leb (n m : nat) : bool :=
  match n,m with
    | O, _ => true
    | S _, O => false
    | S n', S m' => leb n' m'
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Definition blt_nat (n m :nat) : bool :=
  leb n m && negb (beq_nat n m).

Example test_blt_nat1: (blt_nat 2 2) = false.
  Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
  Proof. simpl. reflexivity. Qed.

Theorem plus_O_N : forall n : nat, O + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.


Theorem plus_n_O : forall n, n = n + 0.
Proof.
  intros n. simpl. Abort.

Theorem plus_id_example : forall n m:nat,
  n = m -> n + m = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H1.
  rewrite -> plus_1_l.
  rewrite <- H1.
  reflexivity.
Qed.

Theorem plus_1_neq0 : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall(b : bool), f (f b) = b.
  Proof.
    intros. rewrite -> H. rewrite -> H. reflexivity.
  Qed.

Theorem andb_eq_orb :
  forall(b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
  intros [] [].
  - simpl. intros. reflexivity.
  - simpl. intros. rewrite -> H. reflexivity.
  - simpl. intros. rewrite -> H. reflexivity.
  - simpl. intros. reflexivity.
Qed.


Inductive bin : Type :=
| Z : bin
| T : bin -> bin
| I : bin -> bin.

Fixpoint incr (b:bin) : bin :=
  match b with
  | Z => I Z
  | T b' => I b'
  | I b' => T (incr b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | Z => O
  | T b' => 2 * bin_to_nat b'
  | I b' => S (2 * bin_to_nat b')
  end.

Example test_bin_incr1 : bin_to_nat (incr Z) = S O.
Proof. reflexivity. Qed.

Example test_bin_incr2 : bin_to_nat (incr (incr Z)) = S (S O).
Proof. reflexivity. Qed.

Example test_bin_incr3 : bin_to_nat (incr (incr (incr Z))) = 3.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (incr (incr (incr (incr Z)))) = 4.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 : bin_to_nat (incr (incr (incr (incr (incr Z))))) = 5.
Proof. reflexivity. Qed.










 