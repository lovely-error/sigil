-- AFS refinement of the Church Nat, WITHOUT the uip axiom.
-- Construction: Awodey-Frey-Speight, "Impredicative Encodings of (Higher)
-- Inductive Types" (arXiv:1802.02820), section 4, eq. (4.6). The W-level
-- generalization is Bronsveld's thesis (arXiv:2505.13495), W-types chapter.
--
-- The impredicative Church encoding of Nat (nat.sig section B) has fold
-- computation but no dependent induction (Geuvers 2001). AFS recovers it
-- by carving out the subtype of encodings that behave correctly in every
-- algebra:
--
--   Nat := Sigma (nu : Church Nat). Lim'(nu)
--
-- where Lim' says "nu commutes with every algebra homomorphism". The fold
-- rec := first projection applied to the algebra keeps definitional beta
-- rules, and the Lim' certificate supplies the pointwise core of eta.
--
-- This file proves everything that does NOT need the uip axiom:
--   1. Lim' certificates for zero and succ (closed under succ);
--   2. the refined type Nat with zero/succ/rec all checking;
--   3. definitional beta for rec on zero and succ (rfl via conversion);
--   4. numeral computation of rec by conversion alone;
--   5. etaMid, the pointwise engine of eta: AFS reduce eq. (4.7) to the
--      goal "pr1(n Nat succ 0) X f x = n X f x"; here, for f an algebra
--      morphism and every m, one Leibniz-chained certificate instance
--      gives f (rec Nat zero succ m) = rec X x h m.
--
-- The single hole WITHOUT uip: upgrading the first-projection path
--   path NatStar (fst (rec Nat zero succ m)) (fst m)
-- to the pair-level path
--   path Nat m (rec Nat zero succ m)
-- (equivalently eq. (4.7): rec Nat zero succ = id). That upgrade must
-- re-identify two Lim' certificates over the same first component, which
-- is exactly uniqueness of identity proofs in the certificate fiber: AFS
-- get it from their set-level identity convention, Bronsveld assumes UIP
-- as an axiom. With a stuck-neutral uip primitive the bridge is a
-- transport along the fst-path plus the (uip-given) fiber path, then full
-- eta f = rec and nat_ind follow exactly as in the paper. Everything
-- below stays valid; only one bridge def would be added.
--
-- No funext is needed anywhere here: the certificate instance is pure
-- Leibniz bookkeeping plus definitional conversion. The checker never
-- treats distinct path proofs as convertible (examples/fail_k_conv.sig
-- pins that), so no uip-like conversion rule is smuggled in.
--
-- Leibniz path boilerplate (same as nat.sig / funext.sig).
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b
  = \T a b p M v. p M v;
def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a =
  \T a b p. p (\i. path T i a) (id_path T a);
def path_trans : (T:*) -> (a:T) -> (b:T) -> (c:T) -> path T a b -> path T b c -> path T a c =
  \T a b c p q P h. q P (p P h);

-- Church core (seed before step, as in nat.sig section B); quantifies
-- over all of *, i.e. the impredicative bottom universe does the work.
def NatStar : * = (T:*) -> T -> (T -> T) -> T;
def zeroStar : NatStar = \T z s. z;
def succStar : NatStar -> NatStar = \n T z s. s (n T z s);

-- Lim' (AFS eq. (4.6)): nu commutes with every algebra morphism
-- g : source (T, seed x, step s) -> target (U, seed y, step k).
def nlim : (nu:NatStar) -> * =
  \nu. (T:*) -> (U:*) -> (x:T) -> (y:U) -> (s:T -> T) -> (k:U -> U) -> (g:T -> U)
    -> (path U (g x) y)
    -> ((u:T) -> path U (g (s u)) (k (g u)))
    -> path U (g (nu T x s)) (nu U y k);

-- zero* is already a lim element: g (zero* T x s) is g x by beta, so the
-- seed premise is the conclusion itself. Conversion closes it.
def limZero : nlim zeroStar = \T U x y s k g hp hs. hp;

-- succ* preserves lim: the step premise lands at the intermediate element
-- g (nu T x s), and nu's own certificate (moved under k) finishes. Pure
-- Leibniz bookkeeping: no funext, no uip.
def limSucc : (nu:NatStar) -> nlim nu -> nlim (succStar nu) =
  \nu c T U x y s k g hp hs.
    path_trans U (g (s (nu T x s))) (k (g (nu T x s))) (k (nu U y k))
      (hs (nu T x s))
      (c T U x y s k g hp hs
        (\w. path U (k (g (nu T x s))) (k w))
        (id_path U (k (g (nu T x s)))));
-- Certificates for numerals: Lim' is closed under succ* all the way up.
def limTwo : nlim (succStar (succStar zeroStar)) =
  limSucc (succStar zeroStar) (limSucc zeroStar limZero);

-- The refined type: encodings that commute with every algebra morphism.
def Nat : * = (nu:NatStar) and nlim nu;
def zero : Nat = (zeroStar, limZero);
def succ : Nat -> Nat = \m. (succStar (fst m), limSucc (fst m) (snd m));
def one : Nat = succ zero;
def two : Nat = succ one;

-- The fold: first projection applied to the algebra. beta is definitional.
def rec : (X:*) -> X -> (X -> X) -> Nat -> X =
  \X x h m. fst m X x h;

-- beta on zero: rec's pair field plus zero*'s beta reduce to x; one rfl
-- path accepted by conversion.
def beta_zero : (X:*) -> (x:X) -> (h:X -> X) -> path X (rec X x h zero) x =
  \X x h. id_path X x;

-- beta on succ: rec X x h (succ m) reduces to h (rec X x h m).
def beta_succ : (X:*) -> (x:X) -> (h:X -> X) -> (m:Nat) ->
  path X (rec X x h (succ m)) (h (rec X x h m)) =
  \X x h m. id_path X (h (fst m X x h));

-- Numerals compute through rec by conversion alone (no casing, no
-- funext): rec Nat zero succ ((succStar z*, c) ...) unwinds fst/snd of
-- checked pairs down to zero*, then iterates succ*definitional.
def recTwo : path Nat (rec Nat zero succ two) two = id_path Nat two;

-- etaMid, the pointwise engine of eta (this is the goal AFS reach inside
-- the eq. (4.7) proof, "pr1(n Nat succ 0) X f x = n X f x"): given f with
-- the algebra-morphism premises exactly as Lim' wants them, m's own
-- certificate, applied at source (Nat, zero, succ) and target (X, x, h),
-- IS the statement. fst-definitional side reduces back to rec.
def etaMid : (X:*) -> (x:X) -> (h:X -> X) -> (f:Nat -> X) ->
  (path X (f zero) x) ->
  ((u:Nat) -> path X (f (succ u)) (h (f u))) ->
  (m:Nat) -> path X (f (rec Nat zero succ m)) (rec X x h m) =
  \X x h f hp hs m. (snd m : nlim (fst m)) Nat X zero x succ h f hp hs;

-- Stopping point. To close eq. (4.7) and nat_ind one needs exactly the
-- pair-level upgrade discussed in the header: a stuck-neutral uip
-- primitive of the shape
--   uip : (A:*) -> (a:A) -> path (path A a a) p q
-- over the Leibniz path (reserved constant, architected like quot_sound,
-- conversion untouched so fail_k_conv.sig stays red). With it, define the
-- fiber-prop bridge path Nat m (rec Nat zero succ m), get full eta
-- f = rec via funext from etaMid's pointwise statement, and nat_ind via
-- the AGS12 uniqueness-of-the-recursor lemma. Zero changes to the defs
-- above would be required.
