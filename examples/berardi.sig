-- Berardi's paradox in sigil-neo: excluded middle on `*` is refutable.
--
-- `not_em : EM -> Void` checks. So `*` cannot be made classical: adding
-- `axiom em : (P:*) -> P or (P -> Void)` would give a closed term of `Void`.
-- (The system itself stays consistent: `em` is only a hypothesis here.)
--
-- Ingredients, none of them exotic:
--   * `*` is impredicative, so `Bool`, `pow P = P -> Bool`, and
--     `Univ = (P:*) -> pow P` all live in `*`;
--   * `A or B : *` for `A B : *` and `either_rect` has dependent
--     elimination into `*` (the AC_IF step; Coq's Prop has this too);
--   * `either_rect` ALSO eliminates into families `* -> *`-valued, so the two
--     elements of `Bool = Unit or Unit` are provably distinct: this is the
--     "strong elimination of an inductive proposition" that Coq forbids and
--     that turns Barbanera-Berardi's `tt = ff` into a contradiction.
--
-- Follows theories/Logic/Berardi.v of the Coq standard library.

-- Leibniz equality (copied from path.sig)
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b =
  \T a b p M v. p M v;
def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a =
  \T a b p. p (\i. path T i a) (id_path T a);
def path_trans : (T:*) -> (a:T) -> (b:T) -> (c:T) -> path T a b -> path T b c -> path T a c =
  \T a b c p q. q (\t. path T a t) p;

-- Excluded middle over `*` (a hypothesis, never an axiom of the system)
def EM : * = (P:*) -> P or (P -> Void);

-- Two distinct booleans in `*`
def Bool : * = Unit or Unit;
def tt : Bool = inl ();
def ff : Bool = inr ();

-- tt and ff are distinct (large elimination of `or` into a `*`-valued family)
def tt_ne_ff : path Bool tt ff -> Void =
  \p. p (\b. match b return (\_. *) { inl _ => Unit | inr _ => Void }) ();

-- IFProp and AC_IF
def ifp : (em:EM) -> (B:*) -> (C:*) -> C -> C -> C =
  \em B C e1 e2. either_rect B (B -> Void) (\_. C) (\_. e1) (\_. e2) (em B);

def ac_if : (em:EM) -> (B:*) -> (C:*) -> (e1:C) -> (e2:C) -> (Q:(C -> *)) ->
  (B -> Q e1) -> ((B -> Void) -> Q e2) -> Q (ifp em B C e1 e2) =
  \em B C e1 e2 Q h1 h2.
    either_rect B (B -> Void)
      (\w. Q (either_rect B (B -> Void) (\_. C) (\_. e1) (\_. e2) w))
      (\b. h1 b) (\nb. h2 nb) (em B);

-- Power set into Bool, and retracts
def pow : * -> * = \A. A -> Bool;

def retract : (A:*) -> (B:*) -> * =
  \A B. (i : A -> B) and ((j : B -> A) and ((a:A) -> path A (j (i a)) a));

def retract_cond : (A:*) -> (B:*) -> * =
  \A B. (i2 : A -> B) and ((j2 : B -> A) and (retract A B -> (a:A) -> path A (j2 (i2 a)) a));

def ac : (A:*) -> (B:*) -> (r:retract_cond A B) -> retract A B -> (a:A) ->
  path A (fst (snd r) (fst r a)) a =
  \A B r rt. snd (snd r) rt;

def id_ret : (A:*) -> retract A A =
  \A. ((\x. x), ((\x. x), (\a. id_path A a)));

-- L1: classically, (pow A) is a "conditional retract" of (pow B)
def L1 : (em:EM) -> (A:*) -> (B:*) -> retract_cond (pow A) (pow B) =
  \em A B.
    either_rect (retract (pow A) (pow B)) (retract (pow A) (pow B) -> Void)
      (\_. retract_cond (pow A) (pow B))
      (\r. (fst r, (fst (snd r), (\_. snd (snd r)))))
      (\hf. ((\x y. ff), ((\x y. ff), (\r a. absurd (path (pow A) (\y. ff) a) (hf r)))))
      (em (retract (pow A) (pow B)));

-- The paradoxical set and its "bijection" with pow Univ
def Univ : * = (P:*) -> pow P;
def fU : Univ -> pow Univ = \u. u Univ;
def gU : EM -> pow Univ -> Univ =
  \em h X. (fst (snd (L1 em X Univ))) ((fst (L1 em Univ Univ)) h);

def fg : (em:EM) -> (h:pow Univ) -> path (pow Univ) (fU (gU em h)) h =
  \em h. ac (pow Univ) (pow Univ) (L1 em Univ Univ) (id_ret (pow Univ)) h;

-- Russell
def notb : EM -> Bool -> Bool =
  \em b. ifp em (path Bool b tt) Bool ff tt;
def phi : (em:EM) -> pow Univ = \em u. notb em (u Univ u);
def Rus : (em:EM) -> Univ = \em. gU em (phi em);

def not_fix : (em:EM) -> path Bool (Rus em Univ (Rus em)) (notb em (Rus em Univ (Rus em))) =
  \em. path_subst (pow Univ) (fU (Rus em)) (phi em) (fg em (phi em))
         (\k. path Bool (fU (Rus em) (Rus em)) (k (Rus em)))
         (id_path Bool (fU (Rus em) (Rus em)));

-- Classical proof irrelevance: tt = ff
def berardi : EM -> path Bool tt ff =
  \em.
    ac_if em (path Bool (Rus em Univ (Rus em)) tt) Bool ff tt
      (\y. path Bool (Rus em Univ (Rus em)) y -> path Bool tt ff)
      (\pxt pxf. path_trans Bool tt (Rus em Univ (Rus em)) ff
                   (path_symm Bool (Rus em Univ (Rus em)) tt pxt) pxf)
      (\nb pxt. absurd (path Bool tt ff) (nb pxt))
      (not_fix em);

-- The contradiction
def not_em : EM -> Void = \em. tt_ne_ff (berardi em);
