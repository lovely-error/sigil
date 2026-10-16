-- Natural numbers, two derivations (see docs for the full analysis).
--
-- Leibniz path (for the computation proofs at the end of each section).
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b
  = \T a b p M v. p M v;
def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a
  = \T a b p. p (\i. path T i a) (id_path T a);
--
-- A. W-DERIVED Nat (structural): W with boolean labels and a *split*
--    family (`B(inl)=Void`, `B(inr)=Unit`) written with `match`. Formation,
--    introduction, AND non-dependent recursion check: the `w_rect` step
--    splits on the label with `match`, and branch refinement substitutes the
--    pattern into `ih`'s type — where the canonical pattern makes the stuck
--    family reduce by iota (`Bf (inr b) ≡ Unit`, so `ih ()` fits). Plain
--    `either_rect` cannot do this (no refinement: `ih` keeps type `Bf a`
--    over neutral `a`, and `ih ()` fails) — dependent `match` is exactly
--    the missing piece the old wall analysis predates.
--    Dependent induction (`nat_ind`, section C below) goes through with
--    transports in both branches — funext derived from quotients plus
--    Unit-eta — and one structural trick (the inner `match` motive
--    generalizes over every scrutinee-dependent premise, since `f : Bf a`
--    cannot fit `Bf a2` for abstract `a2`). No new axioms, no exactness:
--    the only axiom in play remains `quot_sound`.
def Bool : * = Unit or Unit;
def Bf : Bool -> * = \b. match b return (\_. *) { inl _ => Void | inr _ => Unit };
def WNat : * = W Bool Bf;
def wzero : WNat = sup Bool Bf (inl ()) (\x. absurd WNat x);
def wsucc : WNat -> WNat = \n. sup Bool Bf (inr ()) (\_. n);
def wone : WNat = wsucc wzero;
def wtwo : WNat = wsucc wone;
-- Non-dependent recursion: the step matches on the label; refinement plus
-- iota makes `ih ()` fit in the `inr`-branch, `z` fits the `inl`-branch.
def nat_rec : (P:*) -> P -> (P -> P) -> WNat -> P
  = \P z st w. w_rect Bool Bf (\_. P) (\a f ih. match a return (\_. P) { inl _ => z | inr u => st (ih ()) }) w;
-- It computes: `copy (succ n) ≡ succ (copy n)` by iota chains alone.
def copy : WNat -> WNat = nat_rec WNat wzero wsucc;
def copyBeta : path WNat (copy wone) wone = id_path WNat wone;
def copyBeta2 : path WNat (copy wtwo) wtwo = id_path WNat wtwo;
--
-- C. DEPENDENT INDUCTION (`nat_ind`): needs transports in both branches —
--    funext (pointwise-equal functions have equal classes by `quot_sound`;
--    transporting reflexivity along the class-path gives the function-path,
--    conversion closing by iota-under-eta — no exactness used) and Unit-eta
--    (definitional uniqueness of `()`). Plus one structural trick: the inner
--    `match` motive generalizes over every scrutinee-dependent premise
--    (`f2`, `ih2` as motive binders — McBride-style), because `f : Bf a`
--    cannot fit `Bf a2` for abstract `a2`; branches prove the generic case
--    and the result applies to the outer terms.
def ueta : (u:Unit) -> path Unit u () = \u. id_path Unit u;
def PEq : (A:*) -> (B:*) -> ((A -> B) -> (A -> B) -> *) =
  \A B f g. (x:A) -> path B (f x) (g x);
def ExtEqFun : (A:*) -> (B:*) -> * =
  \A B. Quot (A -> B) (PEq A B);
def ext_fun_app : (A:*) -> (B:*) -> (q:ExtEqFun A B) -> (x:A) -> B =
  \A B q x. quot_lift (A -> B) (PEq A B) B (\f. f x) (\f g pw. pw x) q;
def fext : (A:*) -> (B:*) -> (f:(A -> B)) -> (g:(A -> B)) -> ((x:A) -> path B (f x) (g x)) -> path (A -> B) f g
  = \A B f g p. path_subst (ExtEqFun A B) (quot_mk f : ExtEqFun A B) (quot_mk g : ExtEqFun A B) (quot_sound (A -> B) (PEq A B) f g p) (\c. path (A -> B) (ext_fun_app A B (quot_mk f : ExtEqFun A B)) (ext_fun_app A B c)) (id_path (A -> B) (ext_fun_app A B (quot_mk f : ExtEqFun A B)));
-- `inl`-branch transport (payload by Unit-eta, child function by funext).
def inlTransport : (P:(WNat -> *)) -> (z:P wzero) -> (f:(Void -> WNat)) -> (u:Unit) -> P (sup Bool Bf (inl u) f)
  = \P z f u. path_subst Unit () u (path_symm Unit u () (ueta u)) (\u2. P (sup Bool Bf (inl u2) f)) (path_subst (Void -> WNat) (\x. absurd WNat x) f (path_symm (Void -> WNat) f (\x. absurd WNat x) (fext Void WNat f (\x. absurd WNat x) (\x. absurd (path WNat (f x) (absurd WNat x)) x))) (\g. P (sup Bool Bf (inl () : Unit or Unit) g)) z);
-- `inr`-branch transport (payload by Unit-eta, `f ~ \_. f ()` by funext over
-- pointwise Unit-eta congruence).
def inrTransport : (P:(WNat -> *)) -> (st:(n:WNat) -> P n -> P (wsucc n)) -> (f:(Unit -> WNat)) -> (ih:(u:Unit) -> P (f u)) -> (u:Unit) -> P (sup Bool Bf (inr u) f)
  = \P st f ih u. path_subst Unit () u (path_symm Unit u () (ueta u)) (\u2. P (sup Bool Bf (inr u2) f)) (path_subst (Unit -> WNat) (\_. f ()) f (fext Unit WNat (\_. f ()) f (\u2. path_symm WNat (f ()) (f u2) (path_subst Unit u2 () (ueta u2) (\u3. path WNat (f u3) (f ())) (id_path WNat (f ()))))) (\g. P (sup Bool Bf (inr () : Unit or Unit) g)) (st (f ()) (ih ())));
-- Dependent induction: `w_rect` step splits on the label under a generalized
-- motive; each branch is a transport lemma above.
def nat_ind : (P:(WNat -> *)) -> P wzero -> ((n:WNat) -> P n -> P (wsucc n)) -> (w:WNat) -> P w
  = \P z st w. w_rect Bool Bf P (\a f ih. match a return (\a2. (f2 : Bf a2 -> WNat) -> ((b:Bf a2) -> P (f2 b)) -> P (sup Bool Bf a2 f2)) { inl u => \f2 ih2. inlTransport P z f2 u | inr u => \f2 ih2. inrTransport P st f2 ih2 u } f ih) w;
--
-- B. CHURCH Nat (computational): impredicative iteration bakes recursion in
--    (Pi into `*` from any domain admits it). Closed numerals compute definitionally by beta
--    alone — no casing, no funext, no new primitives. Dependent induction
--    still missing (Geuvers: not derivable for Church encodings).

def Nat : * = (T:*) -> T -> (T -> T) -> T;
def zero : Nat = \T z s. z;
def succ : Nat -> Nat = \n T z s. s (n T z s);
def one : Nat = succ zero;
def two : Nat = succ one;
def plus : Nat -> Nat -> Nat = \m n T z s. m T (n T z s) s;

-- `plus one one` computes to `two` definitionally.
def plus11 : path Nat (plus one one) two = id_path Nat two;
--
-- D. ADDITION ON WNat AND COMMUTATIVITY (by `nat_ind`): Wiesnet-addition
--    plus the right-identity / right-successor lemmas. The step goals
--    (`P (wplus (wsucc n) wzero)` and friends) force `w_rect` iota on open
--    terms through the `nat_rec` global — the eliminator rebuild must keep
--    free variables resolving to their own levels (mirror environment), or
--    a type lands in a term slot and the annotation fails to check.
def wplus : WNat -> WNat -> WNat = \m n. nat_rec WNat n wsucc m;
def congr_succ : (a:WNat) -> (b:WNat) -> path WNat a b -> path WNat (wsucc a) (wsucc b)
  = \a b p P h. p (\x. P (wsucc x)) h;
def path_trans : (T:*) -> (a:T) -> (b:T) -> (c:T) -> path T a b -> path T b c -> path T a c
  = \T a b c p q P h. q P (p P h);
def wplus_zero_right : (n:WNat) -> path WNat (wplus n wzero) n
  = \n. nat_ind (\k. path WNat (wplus k wzero) k) (id_path WNat wzero) (\n ih. congr_succ (wplus n wzero) n ih) n;
def wplus_succ_right : (n:WNat) -> (m:WNat) -> path WNat (wplus n (wsucc m)) (wsucc (wplus n m))
  = \n m. nat_ind (\k. path WNat (wplus k (wsucc m)) (wsucc (wplus k m))) (id_path WNat (wsucc (wplus wzero m))) (\k ih. congr_succ (wplus k (wsucc m)) (wsucc (wplus k m)) ih) n;
def wplus_comm_base : (m:WNat) -> path WNat (wplus wzero m) (wplus m wzero)
  = \m. path_trans WNat (wplus wzero m) m (wplus m wzero) (id_path WNat m) (path_symm WNat (wplus m wzero) m (wplus_zero_right m));
def wplus_comm_step : (m:WNat) -> (k:WNat) -> path WNat (wplus k m) (wplus m k) -> path WNat (wplus (wsucc k) m) (wplus m (wsucc k))
  = \m k ih. path_trans WNat (wplus (wsucc k) m) (wsucc (wplus k m)) (wplus m (wsucc k)) (id_path WNat (wsucc (wplus k m))) (path_trans WNat (wsucc (wplus k m)) (wsucc (wplus m k)) (wplus m (wsucc k)) (congr_succ (wplus k m) (wplus m k) ih) (path_symm WNat (wplus m (wsucc k)) (wsucc (wplus m k)) (wplus_succ_right m k)));
def wplus_comm : (n:WNat) -> (m:WNat) -> path WNat (wplus n m) (wplus m n)
  = \n m. nat_ind (\k. path WNat (wplus k m) (wplus m k)) (wplus_comm_base m) (wplus_comm_step m) n;
