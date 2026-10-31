-- Definitional Leibniz equality, living in `*`, eliminating definitionally.
-- Motive domains are `(T -> *)`-typed: large-domain Pis with `*`-codomains, so
-- impredicativity into `*` keeps every step small. No primitive Eq, no Prop sort.

def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);

def path_subst : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> (M:(T -> *)) -> (v:M a) -> M b =
  \T a b p M v. p M v;

def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;

def path_symm : (T:*) -> (a:T) -> (b:T) -> (p:path T a b) -> path T b a =
  \T a b p. p (\i. path T i a) (id_path T a);

-- Computation rule, holding DEFINITIONALLY: subst-with-refl unfolds
-- (delta through path_subst/id_path, then beta) to `h`, so `id_path`
-- proves it with no further work.
def id_subst : (T:*) -> (v:T) -> (M:(T -> *)) -> (h:M v) -> path (M v) (path_subst T v v (id_path T v) M h) h =
  \T v M h. id_path (M v) h;

-- PMCT eta 1: the polymorphic endomorphism `P v -> P v` is definitionally
-- the identity, so its path is `id_path`.
def pmct_eta_1 : (T:*) -> (v:T) ->
  (p:(P:(T -> *)) -> P v -> P v) ->
  path ((P:(T -> *)) -> P v -> P v) p (\P x. x) =
  \T v p. id_path ((P:(T -> *)) -> P v -> P v) p;

-- The proof below needs function extensionality over the large domain
-- `T -> *`, so the quotient derivation is repeated at `A : Type`
-- (`examples/funext.sig` has the small-domain version).
def PEq : (A:Type) -> (B:(A -> *)) -> ((f:(x:A) -> B x) -> (g:(x:A) -> B x) -> *) =
  \A B f g. (x:A) -> path (B x) (f x) (g x);
def ExtEqFun : (A:Type) -> (B:(A -> *)) -> * =
  \A B. Quot ((x:A) -> B x) (PEq A B);
def ext_fun_app : (A:Type) -> (B:(A -> *)) -> (q:ExtEqFun A B) -> (x:A) -> B x =
  \A B q x. quot_lift ((x:A) -> B x) (PEq A B) (B x) (\f. f x) (\f g pw. pw x) q;
def fext : (A:Type) -> (B:(A -> *)) -> (f:(x:A) -> B x) -> (g:(x:A) -> B x) -> ((x:A) -> path (B x) (f x) (g x)) -> path ((x:A) -> B x) f g
  = \A B f g p. path_subst (ExtEqFun A B) (quot_mk f : ExtEqFun A B) (quot_mk g : ExtEqFun A B) (quot_sound ((x:A) -> B x) (PEq A B) f g p) (\c. path ((x:A) -> B x) (ext_fun_app A B (quot_mk f : ExtEqFun A B)) (ext_fun_app A B c)) (id_path ((x:A) -> B x) (ext_fun_app A B (quot_mk f : ExtEqFun A B)));

-- Forward map used to invert any `p : (P:T -> *) -> P a -> P b`.
def pmct_q1 : (T:*) -> (a:T) -> (b:T) ->
  (p1:(P:(T -> *)) -> P a -> P b) ->
  (Q:(T -> *)) -> Q b -> Q a =
  \T a b p1 Q qb. p1 (\t. Q t -> Q a) (\qa. qa) qb;

-- PMCT eta 2: any two terms of `(P:T -> *) -> P a -> P b` are equal,
-- by inverting one with `pmct_q1` and applying `pmct_eta_1` twice.
def pmct_eta_2 : (T:*) -> (a:T) -> (b:T) ->
  (p1:(P:(T -> *)) -> P a -> P b) ->
  (p2:(P:(T -> *)) -> P a -> P b) ->
  path ((P:(T -> *)) -> P a -> P b) p1 p2 =
  \T a b p1 p2.
    fext (T -> *) (\P. P a -> P b) p1 p2
      (\P. fext (P a) (\x. P b) (p1 P) (p2 P)
        (\x.
          let f1 : (Q:(T -> *)) -> Q a -> Q a = \Q y. pmct_q1 T a b p1 Q (p1 Q y) in
          let f2 : (Q:(T -> *)) -> Q b -> Q b = \Q y. p2 Q (pmct_q1 T a b p1 Q y) in
          let h_a : path (P a) (pmct_q1 T a b p1 P (p1 P x)) x =
            path_subst ((Q:(T -> *)) -> Q a -> Q a) (\Q y. y) f1
              (path_symm ((Q:(T -> *)) -> Q a -> Q a) f1 (\Q y. y) (pmct_eta_1 T a f1))
              (\g. path (P a) (g P x) x) (id_path (P a) x) in
          let h_b : path (P b) (p2 P (pmct_q1 T a b p1 P (p1 P x))) (p1 P x) =
            path_subst ((Q:(T -> *)) -> Q b -> Q b) (\Q y. y) f2
              (path_symm ((Q:(T -> *)) -> Q b -> Q b) f2 (\Q y. y) (pmct_eta_1 T b f2))
              (\g. path (P b) (g P (p1 P x)) (p1 P x)) (id_path (P b) (p1 P x)) in
          path_symm (P b) (p2 P x) (p1 P x)
            (path_subst (P a) (pmct_q1 T a b p1 P (p1 P x)) x h_a
              (\z. path (P b) (p2 P z) (p1 P x)) h_b)));
