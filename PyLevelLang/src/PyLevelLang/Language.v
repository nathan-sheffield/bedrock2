Require Export String.
Require Export ZArith.
Require Export List.
Require Export coqutil.Map.Interface coqutil.Map.SortedListString.
Require Export coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth.

(* Casts one type to another, provided that they are equal
   https://stackoverflow.com/a/52518299 *)
Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f: T -> Type) (x : f T1) :
  f T2 :=
  eq_rect T1 f x T2 H.

(* Add TWord, make TInt a ~bit array *)
Inductive type : Type :=
  | TWord
  | TInt
  | TBool
  | TString
  | TPair (s : string) (t1 t2 : type) (* s = label of t1 in a record *)
  | TEmpty (* "Empty" type: its only value should be the empty tuple () *)
  | TList (t : type).

(* Types whose values can be compared *)
Definition can_eq (t : type) : bool :=
  match t with
  | TWord | TInt | TBool | TString | TEmpty => true
  | _ => false
  end.

Definition type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
decide equality.
apply string_dec.
Defined.

Scheme Boolean Equality for type. (* creates type_beq *)

Declare Scope pylevel_scope. Local Open Scope pylevel_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : pylevel_scope.

(* Primitive literals (untyped) *)
Inductive patom : Type :=
  | PAWord (n : Z)
  | PAInt (n : Z)
  | PABool (b : bool)
  | PAString (s : string)
  | PANil (t : type).

(* Primitive literals (typed) *)
Inductive atom : type -> Type :=
  | AWord (n : Z) : atom TWord
  | AInt (n : Z) : atom TInt
  | ABool (b : bool) : atom TBool
  | AString (s : string) : atom TString
  | ANil (t : type) : atom (TList t)
  | AEmpty : atom TEmpty.

(* Unary operators (untyped) *)
Inductive punop : Type :=
  | PONeg
  | PONot
  | POLength
  | POIntToString.

(* Unary operators (typed) *)
Inductive unop : type -> type -> Type :=
  | OWNeg : unop TWord TWord
  | ONeg : unop TInt TInt
  | ONot : unop TBool TBool
  | OLength : forall t, unop (TList t) TInt
  | OLengthString : unop TString TInt
  | OFst : forall s t1 t2, unop (TPair s t1 t2) t1
  | OSnd : forall s t1 t2, unop (TPair s t1 t2) t2
  | OIntToString : unop TInt TString.

(* Binary operators (untyped) *)
Inductive pbinop : Type :=
  | POPlus
  | POMinus
  | POTimes
  | PODivU
  | PODiv
  | POModU
  | POMod
  | POAnd
  | POOr
  | POConcat
  | POLessU
  | POLess
  | POEq
  | PORepeat
  | POPair
  | POCons
  | PORange.

(* Binary operators (typed) *)
Inductive binop : type -> type -> type -> Type :=
  | OWPlus : binop TWord TWord TWord
  | OPlus : binop TInt TInt TInt
  | OWMinus : binop TWord TWord TWord
  | OMinus : binop TInt TInt TInt
  | OWTimes : binop TWord TWord TWord
  | OTimes : binop TInt TInt TInt
  | OWDivU : binop TWord TWord TWord
  | OWDivS : binop TWord TWord TWord
  | ODiv : binop TInt TInt TInt (* TODO: support option types? *)
  | OWModU : binop TWord TWord TWord
  | OWModS : binop TWord TWord TWord
  | OMod : binop TInt TInt TInt
  | OAnd : binop TBool TBool TBool
  | OOr : binop TBool TBool TBool
  | OConcat : forall t, binop (TList t) (TList t) (TList t)
  | OConcatString : binop TString TString TString
  | OWLessU : binop TWord TWord TBool
  | OWLessS : binop TWord TWord TBool
  | OLess : binop TInt TInt TBool
  | OEq : forall t, can_eq t = true -> binop t t TBool
  | ORepeat : forall t, binop (TList t) TInt (TList t)
  | OPair : forall s t1 t2, binop t1 t2 (TPair s t1 t2)
  | OCons : forall t, binop t (TList t) (TList t)
  | ORange : binop TInt TInt (TList TInt)
  | OWRange : binop TWord TWord (TList TWord).

(* "Pre-expression": untyped expressions from surface-level parsing. *)
Inductive pexpr : Type :=
  | PEVar (x : string)
  | PEAtom (pa : patom)
  | PESingleton (p : pexpr)
  | PEUnop (po : punop) (p : pexpr)
  | PEBinop (po : pbinop) (p1 p2 : pexpr)
  | PEFlatmap (p1 : pexpr) (x : string) (p2 : pexpr)
  | PEFold (p1 : pexpr) (p2 : pexpr) (x : string) (y : string) (p2 : pexpr)
  | PEIf (p1 p2 p3 : pexpr)
  | PELet (x : string) (p1 p2 : pexpr)
  | PERecord (xs : list (string * pexpr))
  | PEProj (p : pexpr) (s : string).

(* Typed expressions. Most of the type checking is enforced in the GADT itself
   via Coq's type system, but some of it needs to be done in the `elaborate`
   function below *)
Inductive expr : type -> Type :=
  | EVar (t : type) (x : string) : expr t
  | ELoc (t : type) (x : string) : expr t
  | EAtom {t : type} (a : atom t) : expr t
  | EUnop {t1 t2 : type} (o : unop t1 t2) (e : expr t1) : expr t2
  | EBinop {t1 t2 t3 : type} (o : binop t1 t2 t3) (e1 : expr t1) (e2: expr t2) : expr t3
  | EFlatmap {t1 t2 : type} (e1 : expr (TList t1)) (x : string) (e2 : expr (TList t2))
      : expr (TList t2)
  | EFold {t1 t2 : type} (e1 : expr (TList t1)) (e2 : expr t2) (x y : string) (e3 : expr t2) : expr t2
  | EIf {t : type} (e1 : expr TBool) (e2 e3 : expr t) : expr t
  | ELet {t1 t2 : type} (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2.

Inductive pcommand : Type :=
  | PCSkip
  | PCSeq (pc1 pc2 : pcommand)
  | PCLet (x : string) (p : pexpr) (pc : pcommand)
  | PCLetMut (x : string) (p : pexpr) (pc : pcommand)
  | PCGets (x : string) (p : pexpr)
  | PCIf (p : pexpr) (pc1 pc2 : pcommand)
  | PCForeach (x : string) (p : pexpr) (pc : pcommand).

Inductive command : Type :=
  | CSkip
  | CSeq (c1 c2 : command)
  | CLet {t : type} (x : string) (e : expr t) (c : command)
  | CLetMut {t : type} (x : string) (e : expr t) (c : command)
  | CGets {t : type} (x : string) (e : expr t)
  | CIf (e : expr TBool) (c1 c2 : command)
  | CForeach {t : type} (x : string) (e : expr (TList t)) (c : command).
