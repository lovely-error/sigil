-- Dependent pairs, predicatively: a Sigma lives with the LARGER of its parts.
-- `(a, b)` means the same product in type position (resolved by mode, not
-- parsing). Projections compute by iota, definitionally.

-- Small Sigmas (all parts small).
def vpair : * = (Void, Void);
def dpair : * = (x : Void) and Void;

-- Introduction and projections.
def mk : (v:Void) -> ((x:Void) and Void) = \v. (absurd Void v, absurd Void v);
def get1 : (p:(x:Void) and Void) -> Void = \p. fst p;
def get2 : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> B (fst p) = \A B p. snd p;

-- Large pairs live in `Type0` (any `Type0` part forces `Type0`) ...
def big : Type = (Void, *);
-- ... but their *components* can still be small types on either side.
def bigdep : (v:Void) -> ((x:Void) and *) = \v. (absurd Void v, Void -> Void);

-- `fst f x` is `(fst f) x`: projections apply through.
def appfst : (f:Void -> Void) -> (v:Void) -> Void = \f v. fst (f, (absurd Void v)) (absurd Void v);

-- The dependent eliminator subsumes the projections: `fst`/`snd` defined
-- from `sig_rect` (all args explicit, `*`-motives).
def fst2 : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> A = \A B p. sig_rect A B (\_. A) (\a b. a) p;
def snd2 : (A:*) -> (B:A -> *) -> (p:(x:A) and B x) -> B (fst p) = \A B p. sig_rect A B (\p. B (fst p)) (\a b. b) p;
