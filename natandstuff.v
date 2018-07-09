Module NatPlayground.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Check nat.
Check S(S(S(O))).

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.


Check pred(O).

End NatPlayground.


Check (S (S (S (S O)))).

Fixpoint evenb (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Example evenodd: evenb 7 = false.
Proof. simpl. reflexivity. Qed.


Example sixnotodd: evenb 6 = true.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) :nat :=
  match n with
  | O => m  
  | S n' => S ( plus n' m)
  end.

Compute plus(2)(3).

