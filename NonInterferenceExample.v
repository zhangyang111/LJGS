Require Export Ch10_Smallstep.

Inductive Sec : Type :=
| L : Sec
| H : Sec
.


(*security type*)
Inductive Ty : Type :=
| an : RawTy -> Sec -> Ty
with RawTy : Type :=
   | int : RawTy
   | fn : Ty -> Ty -> RawTy
.

Definition context := id -> option Ty.
Definition cxEmpty : context := fun _ => None.
Hypothesis ext : context -> Ty -> context.

(* This is the original language with security types*)
Module SecLang.

  Inductive tm : Type :=
  | tvar  : id -> tm 
  | tprot : Sec -> tm -> tm
  | tcon  : nat -> Sec -> tm
  | tabs  : id -> Ty -> tm -> Sec -> tm
  | tapp  : tm -> tm -> tm
  .

  Inductive value : tm -> Prop :=
  | v_c : forall b n,
            value (tcon n b)
  | v_f : forall n T e b,
            value (tabs (Id n) T e b)
  .

  Hypothesis subst : forall (x:id) (s:tm) (t:tm), tm.
  Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

  Hypothesis step : tm -> tm -> Prop.
  Notation "t1  '==>' t2 " := (step (t1) (t2)).

  Hypothesis has_type : context  -> tm -> Ty -> Prop.
End SecLang.

(* In order to show non-interference (NI) we construct a similar
language to the original one, but that removes all high-security
information (i.e. values) *)

Module LowLang.

  Inductive tm : Type :=
  | tvar  : id -> tm 
  | tprot : tm -> tm
  | tcon  : nat -> tm
  | tabs  : id -> Ty -> tm -> tm
  | tapp  : tm -> tm -> tm
  (* The following form is the special one... it will replace all high
     security information, and it can have any high security type. *)
  | tH : tm
  .

  Inductive value : tm -> Prop :=
  | v_c : forall b,
            value (tcon b)
  | v_f : forall n T e,
            value (tabs (Id n) T e)
  | v_H : value tH
  .

  Hypothesis subst : forall (x:id) (s:tm) (t:tm), tm.
  Inductive step : tm -> tm -> Prop :=
  | st_Happ : forall e, value e -> step (tapp tH e) tH
  (* | ... the rest is analogous to SecLang.step *)
  .

  Inductive has_type : context  -> tm -> Ty -> Prop :=
  (* The tH term/value has always a high security type. *)
  | ht_H : forall ctx (rt : RawTy), has_type ctx tH (an rt H)
  (* All other terms have low-security type, e.g. constants: *)
  | ht_int : forall ctx n, has_type ctx (tcon n) (an int L)
  (* | ... and similarly for other terms ...*)
  .

End LowLang.


Module Correspondence.
  (* We project SecLang terms into LowLang terms by replacing high
  security values with tH *)
  Fixpoint project (e : SecLang.tm) : LowLang.tm :=
  match e with
    | SecLang.tvar i => LowLang.tvar i
    | SecLang.tprot L e => LowLang.tprot (project e)
    | SecLang.tprot H _ => LowLang.tH
    | SecLang.tcon n L => LowLang.tcon n
    | SecLang.tcon _ H => LowLang.tH
    | SecLang.tabs n t e L => LowLang.tabs n t (project e)
    | SecLang.tabs _ _ _ H => LowLang.tH
    | SecLang.tapp e1 e2 => LowLang.tapp (project e1) (project e2)
  end.

(* Now we have to show, that SecLang and LowLang are related by projection. First
the typing relations: *)
  Lemma corresp_typing :
    forall ctx e t,
      SecLang.has_type ctx e t ->
      LowLang.has_type ctx (project e) t.
  Admitted.
(* Ok, so when we project well-typed a SecLang term we get a
well-typed LowLang term.*)

  (* When we perform a step in SecLang then we can perform zero or
  more steps in LowLang and get to the same result, modulo projection
  *)
  Lemma corresp_step : forall e e',
                         SecLang.step e e' ->
                         multi (LowLang.step) (project e) (project e').
  Admitted.

  (* We can extend the correspondence to whole
  evaluations: *)
  Lemma corresp_eval : forall e v,
                         SecLang.value v ->
                         multi SecLang.step e v ->
                         multi LowLang.step (project e) (project v).
    Admitted.

    
  (* We now try to show NI for integer values (functions are more
  difficult.. perhaps we'll try them later) *)

  (* It turns out that it is very easy to show NI for LowLang. All high security values are tH *)
  Lemma LowLang_high_term :
    forall v rt,
      LowLang.value v ->
      LowLang.has_type cxEmpty v (an rt H) ->
      v = LowLang.tH.
  Admitted.

  (* Thus, a difference in high security values is no real difference at all: *)
  Corollary NI_LowLang:
    forall id v1  v2 e cx rt,
      LowLang.value v1 ->
      LowLang.value v2 ->
      LowLang.has_type cxEmpty v1 (an rt H) ->
      LowLang.has_type cxEmpty v2 (an rt H) ->
      LowLang.has_type (extend cx id (an rt H)) e (an int L) ->
      LowLang.subst id e v1 = LowLang.subst id e v2
  .
  Admitted. (* Use LowLang_high_term *)


  (* Ok so how does this help? Well, there is a tight relation between
     low-security SecLang and LowLang integers: 

  Firstvalues of low-security integer type are always
  integer constants (and not tH!!) *)
  Lemma LowLang_canonical_low_int:
    forall v cx, LowLang.has_type cx v (an int L) -> exists n, v = LowLang.tcon n.
    Admitted.

  (* Also, there is only one way to get a specific LowLang integer by projection: *)
  Lemma corresp_project_int:
    forall e n, project e = LowLang.tcon n -> e = SecLang.tcon n L.
  Admitted.

  (* Now we have everything: *)
  Theorem NI:
    forall id e v1 v2 w1 w2 cx rt,
      SecLang.value v1 ->
      SecLang.value v2 ->
      SecLang.value w1 ->
      SecLang.value w2 ->
      SecLang.has_type cxEmpty v1 (an rt H) ->
      SecLang.has_type cxEmpty v2 (an rt H) ->
      SecLang.has_type (extend cx id (an rt H)) e (an int L) ->
      multi SecLang.step e[x/v1] w1 ->
      multi SecLang.step e[x/v2] w2 ->
      w1 = w2
  .
  Admitted.
  (* Proceed like this:
     - Let e1 = e[x/v1] and e2 = e[x/v2]
     - use [NI_LowLang] to show that eLow = project (e1) = project (e2)
     - use correspondence to show that eLow -->* [w1] and eLow -->* [w2]
     - use determinism to show that [w1] = [w2]
     - now, use [LowLang_canonical_low_int] and [corresp_project_int]
       to follow the result. *)
End Correspondence.

