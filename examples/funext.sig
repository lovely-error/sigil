-- Function extensionality, DERIVED from quotients (no funext axiom).
-- Dependent version (Lean `fext` is dependent too): pointwise-equal dependent
-- functions have equal classes (`quot_sound` over the pointwise relation);
-- transporting reflexivity along the class-path gives a function-path,
-- because conversion identifies `ext_fun_app (quot_mk f)` with `f`
-- (iota under eta — Lean's `dsimp`+`exact`). No exactness is used anywhere:
-- classes are never unquoted.
--
-- Leibniz path, symmetric transport (for the use at the end).
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b
  = \T a b p M v. p M v;
def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a
  = \T a b p. p (\i. path T i a) (id_path T a);

-- Pointwise relation and its quotient (Lean `PointwiseEq`/`ExtEqFun`).
def PEq : (A:*) -> (B:(A -> *)) -> ((f:(x:A) -> B x) -> (g:(x:A) -> B x) -> *) =
  \A B f g. (x:A) -> path (B x) (f x) (g x);
def ExtEqFun : (A:*) -> (B:(A -> *)) -> * =
  \A B. Quot ((x:A) -> B x) (PEq A B);

-- Class application (Lean `ext_fun_app`): lift with `pw x` respectfulness.
def ext_fun_app : (A:*) -> (B:(A -> *)) -> (q:ExtEqFun A B) -> (x:A) -> B x =
  \A B q x. quot_lift ((x:A) -> B x) (PEq A B) (B x) (\f. f x) (\f g pw. pw x) q;

-- Function extensionality (Lean `fext`): transport reflexivity along soundness.
def fext : (A:*) -> (B:(A -> *)) -> (f:(x:A) -> B x) -> (g:(x:A) -> B x) -> ((x:A) -> path (B x) (f x) (g x)) -> path ((x:A) -> B x) f g
  = \A B f g p. path_subst (ExtEqFun A B) (quot_mk f : ExtEqFun A B) (quot_mk g : ExtEqFun A B) (quot_sound ((x:A) -> B x) (PEq A B) f g p) (\c. path ((x:A) -> B x) (ext_fun_app A B (quot_mk f : ExtEqFun A B)) (ext_fun_app A B c)) (id_path ((x:A) -> B x) (ext_fun_app A B (quot_mk f : ExtEqFun A B)));

-- Use: the `inl`-case transport of WNat induction (needs funext).
def Bool : * = Unit or Unit;
def Bf : Bool -> * = \b. match b return (\_. *) { inl _ => Void | inr _ => Unit };
def WNat : * = W Bool Bf;
def wzero : WNat = sup Bool Bf (inl () : Unit or Unit) (\x. absurd WNat x);
def inlTransport : (P:(WNat -> *)) -> (z:P wzero) -> (f:(Void -> WNat)) -> P (sup Bool Bf (inl () : Unit or Unit) f)
  = \P z f. path_subst (Void -> WNat) (\x. absurd WNat x) f (path_symm (Void -> WNat) f (\x. absurd WNat x) (fext Void (\_. WNat) f (\x. absurd WNat x) (\x. absurd (path WNat (f x) (absurd WNat x)) x))) (\g. P (sup Bool Bf (inl () : Unit or Unit) g)) z;
