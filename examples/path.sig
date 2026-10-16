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
