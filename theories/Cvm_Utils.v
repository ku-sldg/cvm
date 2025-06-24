From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.
Require Import ErrorStringConstants.

Fixpoint peel_n_rawev (n : nat) (ls : RawEv) : Result (RawEv * RawEv) string :=
  match n with
  | 0 => res ([], ls)
  | S n' =>
    match ls with
    | [] => err errStr_peel_n_am
    | x :: ls' =>
      match peel_n_rawev n' ls' with
      | err e => err e
      | res (ls1, ls2) => res (x :: ls1, ls2)
      end
    end
  end.