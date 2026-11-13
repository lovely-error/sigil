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
--    family (`B(inl)=Void`, `B(inr)=Unit`) written with `either_rect`. Formation,
--    introduction, AND non-dependent recursion check: the `w_rect` step
--    eliminates the label with `either_rect`, generalizing the motive over
--    the induction hypothesis (`ih2 : (b:Bf a2) -> P` — convoy pattern) so
--    the canonical pattern makes the family reduce by iota (`Bf (inr b) ≡ Unit`,
--    allowing `ih2 ()` to fit in the `inr` branch).
--    Dependent induction (`nat_ind`, section C below) goes through with
--    transports in both branches — funext derived from quotients plus
--    Unit-eta — and the same structural trick: the inner `either_rect` motive
--    generalizes over every scrutinee-dependent premise (`f2`, `ih2` as
--    motive binders — McBride-style), since `f : Bf a` cannot fit `Bf a2`
--    for abstract `a2`. No new axioms, no exactness: the only axiom in play
--    remains `quot_sound`.
def Bool : * = Unit or Unit;
def Bf : Bool -> * = \b. either_rect Unit Unit (\_. *) (\_. Void) (\_. Unit) b;
def WNat : * = W Bool Bf;
def wzero : WNat = sup Bool Bf (inl ()) (\x. absurd WNat x);
def wsucc : WNat -> WNat = \n. sup Bool Bf (inr ()) (\_. n);
def wone : WNat = wsucc wzero;
def wtwo : WNat = wsucc wone;
-- Non-dependent recursion: the step cases on the label; convoy over ih
-- makes `ih2 ()` fit in the `inr`-branch, `z` fits the `inl`-branch.
def nat_rec : (P:*) -> P -> (P -> P) -> WNat -> P
  = \P z st w. w_rect Bool Bf (\_. P)
      (\a f ih. either_rect Unit Unit (\a2. ((b:Bf a2) -> P) -> P)
                  (\u ih2. z)
                  (\u ih2. st (ih2 ()))
                  a ih)
      w;
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
--    `either_rect` motive generalizes over every scrutinee-dependent premise
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
  = \P z st w. w_rect Bool Bf P
      (\a f ih. either_rect Unit Unit
                  (\a2. (f2 : Bf a2 -> WNat) -> ((b:Bf a2) -> P (f2 b)) -> P (sup Bool Bf a2 f2))
                  (\u f2 ih2. inlTransport P z f2 u)
                  (\u f2 ih2. inrTransport P st f2 ih2 u)
                  a f ih)
      w;
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


def Dec : (A:*) -> * = \A. A or (A -> Void);

-- Large elimination: a type-valued function on WNat, via w_rect with motive (\_. *)
def isZero : WNat -> * =
  \w. w_rect Bool Bf (\_. *) (\a f ih. either_rect Unit Unit (\_. *) (\_. Unit) (\_. Void) a) w;

-- 1. disjointness
def zero_ne_succ : (n:WNat) -> path WNat wzero (wsucc n) -> Void =
  \n p. p isZero ();

-- 2. injectivity, via a predecessor
def wpred : WNat -> WNat =
  \w. w_rect Bool Bf (\_. WNat)
    (\a f ih. either_rect Unit Unit (\a2. (f2 : Bf a2 -> WNat) -> WNat)
                (\u f2. wzero)
                (\u f2. f2 ())
                a f)
    w;
def succ_inj : (n:WNat) -> (m:WNat) -> path WNat (wsucc n) (wsucc m) -> path WNat n m =
  \n m p. p (\x. path WNat n (wpred x)) (id_path WNat n);

-- 3. the decision procedure, by nat_ind on m, then on n
def decEq : (m:WNat) -> (n:WNat) -> Dec (path WNat m n) =
  \m. nat_ind (\m2. (n:WNat) -> Dec (path WNat m2 n))
    (\n. nat_ind (\n2. Dec (path WNat wzero n2))
           (inl (id_path WNat wzero))
           (\k ih. inr (zero_ne_succ k))
           n)
    (\m2 ih n. nat_ind (\n2. Dec (path WNat (wsucc m2) n2))
           (inr (\p. zero_ne_succ m2 (path_symm WNat (wsucc m2) wzero p)))
           (\k ih2. either_rect (path WNat m2 k) (path WNat m2 k -> Void)
                      (\_. Dec (path WNat (wsucc m2) (wsucc k)))
                      (\e. inl (congr_succ m2 k e))
                      (\ne. inr (\h. ne (succ_inj m2 k h)))
                      (ih k))
           n)
    m;