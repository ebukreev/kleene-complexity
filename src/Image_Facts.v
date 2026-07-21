From Coq Require Import Program.Basics.
From Coq Require Import Sets.Powerset Sets.Image.

Lemma Im_singleton : forall U V (f : U -> V) (x : U),
    Im U V (Singleton U x) f = Singleton V (f x).
Proof.
  intros U V f x.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [z Hz y Hy]; destruct Hz; subst; constructor.
  - destruct Hy; apply Im_def; constructor.
Qed.

Lemma Im_union : forall U V (A B : Ensemble U) (f : U -> V),
    Im U V (Union U A B) f = Union V (Im U V A f) (Im U V B f).
Proof.
  intros U V A B f.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [x Hx y Hy]; subst.
    destruct Hx as [x Hx | x Hx]; [left | right]; apply Im_def, Hx.
  - destruct Hy as [y Hy | y Hy]; destruct Hy as [x Hx y Hy]; subst;
      apply Im_def; [left | right]; exact Hx.
Qed.

Lemma Im_id : forall U (X : Ensemble U),
    Im U U X id = X.
Proof.
  intros U X.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [x Hx y Hy]; unfold id in Hy; subst; exact Hx.
  - exact (Im_intro _ _ X id y Hy (id y) eq_refl).
Qed.

Lemma Im_compose : forall U V W (X : Ensemble U) (g : U -> V) (f : V -> W),
    Im V W (Im U V X g) f = Im U W X (fun x => f (g x)).
Proof.
  intros U V W X g f.
  apply Extensionality_Ensembles; split; intros z Hz.
  - destruct Hz as [y Hy z Hz]; destruct Hy as [x Hx y Hy]; subst.
    exact (Im_intro _ _ X (fun x => f (g x)) x Hx _ eq_refl).
  - destruct Hz as [x Hx z Hz]; subst.
    exact (Im_intro _ _ (Im U V X g) f (g x) (Im_intro _ _ X g x Hx _ eq_refl) _ eq_refl).
Qed.
