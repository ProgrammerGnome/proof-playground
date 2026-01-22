Require Import Reals.
Require Import Psatz. (* Automatizáláshoz, ha szükséges *)
Require Import Coquelicot.Coquelicot. (* Opcionális, de modern analízishez jobb *)
Open Scope R_scope.

(* 1. A határérték definíciója *)
Definition is_limit (u : nat -> R) (l : R) :=
  forall eps : R, eps > 0 -> exists N : nat, forall n : nat, 
  (n >= N)%nat -> Rabs (u n - l) < eps.

(* 2. Az unicitási tétel (Egyértelműség) *)
Theorem limit_uniqueness : forall (u : nat -> R) (l1 l2 : R),
  is_limit u l1 -> is_limit u l2 -> l1 = l2.
Proof.
  intros u l1 l2 H1 H2.
  (* Indirekt bizonyítás: tegyük fel, hogy l1 <> l2 *)
  destruct (Req_dec l1 l2) as [Heq | Hneq].
  - (* Ha egyenlők, készen vagyunk *)
    assumption.
  - (* Ha nem egyenlők, ellentmondást keresünk *)
    exfalso.
    (* Legyen eps = |l1 - l2| / 2 *)
    set (eps := Rabs (l1 - l2) / 2).
    assert (Heps_pos : eps > 0).
    { unfold eps. apply Rdiv_lt_0_compat. 
      apply Rabs_pos_lt. assumption. 
      apply Rlt_R0_R2. }
    
    (* Alkalmazzuk a definíciót mindkét határértékre ezzel az eps-sel *)
    specialize (H1 eps Heps_pos).
    specialize (H2 eps Heps_pos).
    
    destruct H1 as [N1 H1].
    destruct H2 as [N2 H2].
    
    (* Vesszük a maximum indexet: N = max(N1, N2) *)
    set (N := max N1 N2).
    
    (* Vizsgáljuk a sorozatot az N. helynél *)
    assert (HN1 : (N >= N1)%nat) by (unfold N; apply Nat.le_max_l).
    assert (HN2 : (N >= N2)%nat) by (unfold N; apply Nat.le_max_r).
    
    specialize (H1 N HN1).
    specialize (H2 N HN2).
    
    (* Háromszög-egyenlőtlenség használata az ellentmondáshoz *)
    (* |l1 - l2| <= |l1 - u N| + |u N - l2| *)
    have H_tri := Rabs_triang (l1 - u N) (u N - l2).
    replace (l1 - u N + (u N - l2)) with (l1 - l2) in H_tri by ring.
    
    (* Átírjuk a távolságokat *)
    rewrite Rabs_minus_sym in H1.
    
    (* Az egyenlőtlenségek összegzése ellentmondásra vezet *)
    assert (H_contra : Rabs (l1 - l2) < eps + eps).
    { eapply Rle_lt_trans. apply H_tri. lra. }
    
    unfold eps in H_contra.
    lra. (* Linear Real Arithmetic solver megoldja: d < d/2 + d/2 -> d < d, ami hamis *)
Qed.
