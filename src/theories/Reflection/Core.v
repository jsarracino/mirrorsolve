
Require Export MetaCoq.Template.All.
(* Require Import MetaCoq.Checker.All. *)

Require Import MetaCoq.Template.Checker.

Definition eq_predicate {T: Type} (eq_T: T -> T -> bool) (l r: predicate T) : bool :=
  forallb2 eq_T l.(pparams) r.(pparams) && eq_T l.(preturn) r.(preturn).

Fixpoint eq_term (l r: term) : bool := 
  match l with
  | tRel n =>
    match r with
    | tRel n' => PeanoNat.Nat.eqb n n'
    | _ => false
    end
  | tVar id => 
    match r with
    | tVar id' => String.eqb id id'
    | _ => false
    end
  | tEvar ev args =>
    match r with
    | tEvar ev' args' => (Nat.eqb ev ev' && forallb2 eq_term args args')%bool
    | _ => false
    end
  | tSort _ =>
    match r with
    | tSort _ => true
    | _ => false
    end
  | tCast f _ T =>
    match r with
    | tCast f' _ T' => (eq_term f f' && eq_term T T')%bool
    | _ => false
    end
  | tProd _ b t0 =>
    match r with
    | tProd _ b' t' => (eq_term b b' && eq_term t0 t')%bool
    | _ => false
    end
  | tLambda _ b t0 =>
    match r with
    | tLambda _ b' t' => (eq_term b b' && eq_term t0 t')%bool
    | _ => false
    end
  | tLetIn _ b t0 c =>
    match r with
    | tLetIn _ b' t' c' => (eq_term b b' && eq_term t0 t' && eq_term c c')%bool
    | _ => false
    end
  | tApp f args =>
    match r with
    | tApp f' args' => (eq_term f f' && forallb2 eq_term args args')%bool
    | _ => false
    end
  | tConst c _ =>
    match r with
    | tConst c' _ => eq_constant c c'
    | _ => false
    end
  | tInd i _ =>
    match r with
    | tInd i' _ => eq_inductive i i'
    | _ => false
    end
  | tConstruct i k _ =>
    match r with
    | tConstruct i' k' _ => (eq_inductive i i' && PeanoNat.Nat.eqb k k')%bool
    | _ => false
    end
  | tCase c_info p c brs =>
      match r with
      | tCase c_info' p' c' brs' =>
        (eq_inductive c_info.(ci_ind) c_info'.(ci_ind) &&
          eq_predicate eq_term p p' && eq_term c c' &&
          forallb2 (fun l r => eq_term l.(bbody) r.(bbody)) brs brs')%bool
      | _ => false
      end
  | tProj p c =>
    match r with
    | tProj p' c' => (eq_projection p p' && eq_term c c')%bool
    | _ => false
    end
  | tFix mfix idx =>
    match r with
    | tFix mfix' idx' =>
      (forallb2
          (fun x y : def term =>
          eq_term (dtype x) (dtype y) &&
          eq_term (dbody x) (dbody y)) mfix mfix' &&
        PeanoNat.Nat.eqb idx idx')%bool
    | _ => false
    end
  | tCoFix mfix idx =>
    match r with
    | tCoFix mfix' idx' =>
      (forallb2
          (fun x y : def term =>
          eq_term (dtype x) (dtype y) &&
          eq_term (dbody x) (dbody y)) mfix mfix' &&
        PeanoNat.Nat.eqb idx idx')%bool
    | _ => false
    end
  end.

Definition eq_ctor (l r: term) : bool := 
  match l, r with 
  | tApp l' _, tApp r' _ => eq_term l' r'
  | tApp l' _, _ => eq_term l' r
  | _, tApp r' _ => eq_term l r'
  | _, _ => false
  end.