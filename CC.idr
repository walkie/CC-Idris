module CC

%default total

-- * Syntax

-- ** Object language.

-- | Plain integer-tagged binary trees.
data Tree : Type where
  TLeaf : Nat -> Tree
  TNode : Nat -> Tree -> Tree -> Tree

-- ** Choice Calculus

Dim : Type
Dim = Nat

Tag : Type
Tag = Bool

L : Tag
L = True

R : Tag
R = False

-- | Syntax of binary choice calculus expressions with global dimensions.
--   The object language is integer-tagged binary trees.
data CC : Type where
  Leaf : Nat -> CC
  Node : Nat -> CC -> CC -> CC
  Chc  : Dim -> CC -> CC -> CC


-- * Semantics

-- | A selection is a total function from a dimension name to the tag to select.
Selection : Type
Selection = Dim -> Tag

-- | Set s(d)=t in selection s.
select : Tag -> Dim -> Selection -> Selection
select t d s d' = if d == d' then t else s d'

-- | Select d.R in all dimensions in the given list, d.L otherwise.
selectR : List Dim -> Selection
selectR = foldr (select R) (\_ => L)

-- | Select d.L in all dimensions in the given list, d.R otherwise.
selectL : List Dim -> Selection
selectL = foldr (select L) (\_ => R)

-- The denotation of a choice calculus expression is a function from
-- selections to plain binary trees.
Denotation : Type
Denotation = Selection -> Tree

-- Denotational semantics of the choice calculus.
sem : CC -> Denotation
sem (Leaf a)     _ = TLeaf a
sem (Node a l r) s = TNode a (sem l s) (sem r s)
sem (Chc  d l r) s = if s d then sem l s else sem r s


-- * Equivalence Laws

ifCase : {b : Bool} -> {P : Type} -> ((b' : True = b) -> P) -> ((b' : False = b) -> P) -> P
ifCase {b = True}  pt _  = pt refl
ifCase {b = False} _  pf = pf refl

ifTrue : {b : Bool} -> {t : a} -> {f : a} ->
         True = b -> (if b then t else f) = t
ifTrue {t} {f} p = replace {P = \b => (if b then t else f) = t} p refl

ifFalse : {b : Bool} -> {t : a} -> {f : a} ->
          False = b -> (if b then t else f) = f
ifFalse {t} {f} p = replace {P = \b => (if b then t else f) = f} p refl

ifIdemp : {t : a} -> {f : a} -> {x : a} ->
          (pt : t = x) -> (pf : f = x) -> (if c then t else f) = x
ifIdemp {c} = ifCase {b = c} (\ct => ?proof_ifIdempT) (\cf => ?proof_ifIdempF)
-- ifIdemp {c = True}  pt _  = pt refl
-- ifIdemp {c = False} _  pf = pf refl

ifDomT : {tt : a} -> {tf : a} -> {f : a} ->
         (if c then (if c then tt else tf) else f) = if c then tt else f
ifDomT {c = True}  = refl
ifDomT {c = False} = refl

ifDomF : {t : a} -> {ft : a} -> {ff : a} ->
         (if c then t else (if c then ft else ff)) = if c then t else ff
ifDomF {c = True}  = refl
ifDomF {c = False} = refl

{-
using (e : CC, e1 : CC, e2 : CC, e3 : CC, e4 : CC,
       d : Dim, d1 : Dim, d2 : Dim, s : Selection)
-}

{-
ifCase : {t1 : a} -> {f1 : a} -> {t2 : a} -> {f2 : a} ->
         (c1 = c2) -> (t1 = t2) -> (f1 = f2) ->
         (if c1 then t1 else f1) = if c2 then t2 else f2
ifCase pc pt pf = ?proof_ifCase
-}

-- | Two expressions are semantically equivalent if they yield the same
--   plain trees for all possible selections.
equiv : CC -> CC -> Selection -> Type
equiv e1 e2 s = sem e1 s = sem e2 s

syntax [e1] "<=>" [e2] = equiv e1 e2 s

-- | Choice idempotency
cIdemp : (Chc d e e) <=> e
cIdemp = ifEq
  where
    ifEq : {x : a} -> (if c then x else x) = x
    ifEq {c = True}  = refl
    ifEq {c = False} = refl

cIdemp' : (Chc d e e) <=> e
cIdemp' {s} {d} = ifCase {b = s d} ifTrue ifFalse

-- | C-C-Merge with nested choice in left alternative.
ccMergeL : (Chc d (Chc d e1 e2) e3) <=> (Chc d e1 e3)
ccMergeL = ifDomT
  where
    ifDomT : {tt : a} -> {tf : a} -> {f : a} ->
             (if c then (if c then tt else tf) else f) = if c then tt else f
    ifDomT {c = True}  = refl
    ifDomT {c = False} = refl

ccMergeL' : (Chc d (Chc d e1 e2) e3) <=> (Chc d e1 e3)
ccMergeL' {s} {d} = ifCase {b = s d} ?proof_sd ?proof_sd

-- | C-C-Merge with nested choice in left alternative.
ccMergeR : (Chc d e1 (Chc d e2 e3)) <=> (Chc d e1 e3)
ccMergeR = ifDomF
  where
    ifDomF : {t : a} -> {ft : a} -> {ff : a} ->
             (if c then t else (if c then ft else ff)) = if c then t else ff
    ifDomF {c = True}  = refl
    ifDomF {c = False} = refl

ccMergeR' : (Chc d e1 (Chc d e2 e3)) <=> (Chc d e1 e3)
ccMergeR' {s} {d} = ifCase {b = s d} ?proof_sd ?proof_sd

-- | C-C-Swap with nested choice in left alternative of simpler form.
ccSwapL : (Chc d' (Chc d e1 e3) (Chc d e2 e3)) <=> Chc d (Chc d' e1 e2) e3
ccSwapL = ifPushL
  where
    ifPushL : {tt : a} -> {tf : a} -> {f : a} ->
              (if c' then (if c then tt else f) else (if c then tf else f)) =
              (if c then (if c' then tt else tf) else f)
    ifPushL {c = True}  {c' = True}  = refl
    ifPushL {c = True}  {c' = False} = refl
    ifPushL {c = False} {c' = True}  = refl
    ifPushL {c = False} {c' = False} = refl

ccSwapL' : (Chc d' (Chc d e1 e3) (Chc d e2 e3)) <=> Chc d (Chc d' e1 e2) e3
ccSwapL' {s} {d} {d'} = ifCase {b = s d'} (ifCase {b = s d} ?proof_sd ?proof_sd) ?proof_sd

-- | C-C-Swap with nested choice in right alternative of simpler form.
ccSwapR : (Chc d' (Chc d e1 e2) (Chc d e1 e3)) <=> Chc d e1 (Chc d' e2 e3)
ccSwapR = ifPushR
  where
    ifPushR : {t : a} -> {ft : a} -> {ff : a} ->
              (if c' then (if c then t else ft) else (if c then t else ff)) =
              (if c then t else (if c' then ft else ff))
    ifPushR {c = True}  {c' = True}  = refl
    ifPushR {c = True}  {c' = False} = refl
    ifPushR {c = False} {c' = True}  = refl
    ifPushR {c = False} {c' = False} = refl

-- | C-S with choice in left branch of simpler form.
csL : (Chc d (Node a e1 e3) (Node a e2 e3)) <=> Node a (Chc d e1 e2) e3
csL = prf
  where
    prf : {a : Nat} -> {t1 : Tree} -> {t2 : Tree} -> {t3 : Tree} ->
          (if c then TNode a t1 t3 else TNode a t2 t3) =
          (TNode a (if c then t1 else t2) t3)
    prf {c = True}  = refl
    prf {c = False} = refl

---------- Proofs ----------

proof_ifIdempT = proof
  intros
  rewrite ct
  compute
  rewrite pt
  trivial

proof_ifIdempF = proof
  intros
  rewrite cf
  compute
  rewrite pf
  trivial

proof_sd = proof { intros; rewrite b'; compute; trivial }

-- CC.proof_ifCase = proof { intros; rewrite pc; rewrite pt; rewrite pf; trivial }


