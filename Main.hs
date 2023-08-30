{-# LANGUAGE
  UnicodeSyntax, TypeOperators, DeriveFoldable,
  LambdaCase, NamedFieldPuns #-}

import qualified Data.Set as Set
import qualified Data.List as List
type Set = Set.Set

-------------------------------------------------
-- 1.1. Expressions and Symbols
-------------------------------------------------
type Expr = String
-- just record the arity of the symbol, not the type.
data Symbol = Sym { name ∷ String, arity ∷ Int, syn ∷ Expr }
  deriving Ord

instance Eq Symbol where
  (==) x y = (name x == name y) && (arity x == arity y)

instance Show Symbol where
  show (Sym{name,arity,syn}) = syn

fill_expr ∷ Expr → Expr → Expr
fill_expr m1 m2 =
    let (hd,tl) = break (=='▢') m1
    in (hd ++ m2 ++ tail tl)

fill_list ∷ Expr → [Expr] → Expr
fill_list = foldl fill_expr

-------------------------------------------------
-- 1.2. Types
-------------------------------------------------
data Type = TCon Symbol [Type] | TVar Int
  deriving (Eq, Ord)

instance Show Type where
  show (TCon (Sym{name,arity,syn}) typs) =
    if arity == length typs then
      fill_list syn (map show typs)
    else
      error "Length of list (" ++ show typs ++ ") does not match arity ("++ show arity ++") of " ++ show name
  show (TVar i) = "𝐭𝐯" ++ show i

-- Get set of type variables indexes occurring in type.
tvars_typ ∷ Type → Set Int
tvars_typ (TCon sym xs) = Set.unions (map tvars_typ xs)
tvars_typ (TVar i) = Set.singleton i

-------------------------------------------------
-- 1.3. Raw Terms
-------------------------------------------------
type VName = (String, Type)
type CName = (Symbol, Type)
data RawTerm =
    RVar VName
  | RConst CName
  | RApp RawTerm RawTerm
  | RLam VName RawTerm

instance Show RawTerm where
  show (RVar x) = fst x
  show (RConst x)   = show (fst x)
  show (RApp t1 t2) =
    let
      (e1,e2) = (show t1, show t2) in
    if elem '▢' (show t1)
      then fill_expr e1 e2
      else "(" ++ e1 ++ " " ++ e2 ++ ")"
  show (RLam x@(_,typ) trm) =
    "(λ" ++ show (RVar x) ++ " ∷ " ++ show typ ++ ". " ++ show trm ++ ")"

-- Attempt to generate type of raw term.
typ_of_raw ∷ RawTerm → Type
typ_of_raw (RVar   (_,typ)) = typ
typ_of_raw (RConst (_,typ)) = typ
typ_of_raw t@(RApp t1 t2)  = case typ_of_raw t1 of
  TCon sym xs ->
    if (name sym == "fn")
      then (last xs)
      else error $
        "Term " ++ show t1 ++ " in " ++ show t ++ " is not of arrow type."
  _ -> error "type error"
typ_of_raw (RLam (_,typ) trm) = (typ ⟹ typ_of_raw trm)

-- Return set of free variables occurring in term.
fvars_raw ∷ RawTerm → Set VName
fvars_raw trm = case trm of
  RVar x     → Set.singleton x
  RConst _   → Set.empty
  RApp t1 t2 → Set.union (fvars_raw t1) (fvars_raw t2)
  RLam x t   → Set.delete x (fvars_raw t)

-- Return set of type variable idxs occurring in term.
tvars_raw ∷ RawTerm → Set Int
tvars_raw trm = case trm of
  RApp t1 t2 → Set.union (tvars_raw t1) (tvars_raw t2)
  RLam x t   → Set.union (tvars_raw (RVar x)) (tvars_raw t)
  RVar (_,typ) → tvars_typ typ
  RConst (_,typ) → tvars_typ typ

-------------------------------------------------------------------------------
--- 1.4. Terms
-------------------------------------------------------------------------------
-- `Term` is the datatype we will actually use for performing operations.
data Term =
    Var VName
  | Bound Int
  | Const CName
  | App Term Term
  | Abs VName Term
  deriving (Eq, Ord)

instance Show Term where
  show = show . conv_trm

typ_of ∷ Term → Type
typ_of = typ_of_raw . conv_trm

fvars ∷ Term → Set Term
fvars = (Set.map Var) . fvars_raw . conv_trm

tvars ∷ Term → Set Type
tvars = (Set.map TVar) . tvars_raw . conv_trm

subst ∷ Term → (VName, Term) → Term
subst trm sub@(y,b) = case trm of
  Bound i → Bound i
  Var x → if (x == y) then b else (Var x)
  Const k → Const k
  App t1 t2 → App (subst t1 sub) (subst t2 sub)
  Abs x c → Abs x (subst c sub)

-- Convert from nameless to nameful representation.
open ∷ Term → Term → Term
open t u = go 0 u t
  where
    go k u (Var x) = Var x
    go k u (Const x) = Const x
    go k u (Bound i) = if i == k then u else (Bound i)
    go k u (App t1 t2) = App (go k u t1) (go k u t2)
    go k u (Abs x t) = Abs x (go (k + 1) u t)

bconv ∷ Term → Term
bconv (App (Abs _ t1) t2) = open t1 t2
bconv t = t

conv_trm :: Term -> RawTerm
conv_trm t = conv_term' [] t
  where
    conv_term' :: [VName] -> Term -> RawTerm
    conv_term' ctx (Var x)     = RVar x
    conv_term' ctx (Bound i)   = RVar (ctx !! i) -- fetch from context
    conv_term' ctx (Const k)   = RConst k
    conv_term' ctx (App t1 t2) = RApp (conv_term' ctx t1) (conv_term' ctx t2)
    conv_term' ctx (Abs x t)   = RLam x (conv_term' (x : ctx) t)




-- -- Typing on terms
-- type Typing = (Term, Type)
-- -- convert to raw term, obtain typing
-- var_typ ∷ VName → Typing
-- var_typ x@(v,t) = (Var x, t)

-- con_typ ∷ CName → Typing
-- con_typ k@(s,t) = (Const k, t)

-- app_typ ∷ Typing → Typing → Typing
-- app_typ (b, t1) (c, t2) = case t1 of
--   TVar _      → error $ "Error. " ++ show t1 ++ " not of arrow type."
--   TCon sym ts →
--     if (name sym == "fn") then
--       (App b c, last ts)
--     else error $ "Error. " ++ show t1 ++ " not of arrow type."

-- abs_typ ∷ VName → Typing → Typing
-- abs_typ (v,t1) (b,t2) = (Abs v b, t1 ⟹ t2)


conv_raw :: RawTerm -> Term
conv_raw = conv_raw' []

conv_raw' :: [VName] -> RawTerm -> Term
conv_raw' vs (RVar x) =
  case List.elemIndex x vs of
    Just idx -> Bound idx
    Nothing  -> Var x
conv_raw' _ (RConst k) = Const k
conv_raw' vs (RApp t1 t2) = App (conv_raw' vs t1) (conv_raw' vs t2)
conv_raw' vs (RLam x t)   = Abs x (conv_raw' (x : vs) t)



ifix ∷ String → Expr
ifix op = "(▢ " ++ op ++ " ▢)"

dom_sym ∷ Int -> Symbol
dom_sym i = Sym {name = "dom", arity = 0, syn = "𝐝" ++ show i}
dom i = TCon (dom_sym i) []

bool_sym, fn_sym, mem_sym ∷ Symbol
bool_sym = Sym {name = "bool", arity = 0, syn = "⭐"}
bool = TCon bool_sym []

fn_sym   = Sym {name = "fn",   arity = 2, syn = ifix "⇒"}
(⟹) ∷ Type → Type → Type
t1 ⟹ t2 = TCon fn_sym [t1,t2]

v_sym = Sym {name="v_typ", arity= 0, syn= "𝐕"}
v_typ = TCon v_sym []

mem_sym = Sym {name = "mem",  arity = 2, syn = ifix "∈"}
mem_const = Const (mem_sym, v_typ ⟹ v_typ ⟹ bool)
mem x y = App (App mem_const x) y

-- Define some example symbols and types for convenience
sym_f = Sym {name = "f", arity = 1, syn = "f"}
sym_g = Sym {name = "g", arity = 1, syn = "g"}
typ_a = TCon (Sym {name = "A", arity = 0, syn = "A"}) []
typ_b = TCon (Sym {name = "B", arity = 0, syn = "B"}) []

-- Define some example terms
term1 = Var ("x", typ_a)
term2 = Const (sym_f, typ_a ⟹ typ_b)
term3 = App term2 term1


term4 = Abs ("x", typ_a) (App (term2) (Bound 0))
term5 = App term4 term1
term6 = App (Abs ("y", typ_b) (Bound 0)) (Var ("z", typ_b))


mem_trm = Abs ("x", v_typ) (Abs ("y", v_typ) (mem (Bound 1) (Bound 0)))
-- Testing fv function
test_fv1 = fvars term1  -- Should return {("x", typ_a)}
test_fv2 = fvars term3  -- Should return {("x", typ_a), ("f", typ_a ⟹ typ_a)}
test_fv3 = fvars term4  -- Should return {("f", typ_a ⟹ typ_a)}

-- Testing subst function
test_subst1 = subst term3 (("x", typ_a), Var ("y", typ_a))  -- Should replace "x" with "y" in term3

-- Testing bconv function
test_bconv1 = bconv term5  -- Should return term3
test_bconv2 = bconv term6  -- Should return Var ("z", typ_b)

