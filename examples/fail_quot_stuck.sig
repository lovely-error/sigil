-- Must FAIL, each independently.
-- Computation gets stuck on the `quot_sound` axiom (it has no iota): a fully
-- applied `quot_sound` with canonical arguments is well-typed but neutral,
-- so anything that must reduce through it fails to convert definitionally.
-- (Contrast `squashBeta` in quot.sig, where `quot_lift` DOES reduce on a
-- canonical `quot_mk`, and the `indUnit` control in the `nat_ind_stuck_at_sound`
-- test, where Unit-eta collapses the stuck chain without reduction.)
def path : (T:*) -> (a:T) -> (b:T) -> * =
  \T a b. (P:(T -> *)) -> (P a) -> (P b);
def id_path : (T:*) -> (v:T) -> path T v v =
  \T v P h. h;
def Bool : * = Unit or Unit;
-- A closed `quot_sound` transport into `Bool` does not reduce to `inl ()`.
def bad1 : path Bool (quot_sound Unit (\_ _. Unit) () () () (\_. Bool) (inl () : Bool)) (inl () : Bool)
  = id_path Bool (inl () : Bool);
-- Stuckness propagates through application: transporting a function and
-- applying it still does not reduce (stuck on the axiom, not on beta).
def bad2 : path Bool ((quot_sound Unit (\_ _. Unit) () () () (\_. Unit -> Bool) (\_. (inl () : Bool))) ()) (inl () : Bool)
  = id_path Bool (inl () : Bool);
