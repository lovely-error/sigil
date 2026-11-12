-- Hurkens' paradox relative to strong excluded middle in *.
-- Predicates are valued in Two : * (so U2 : * and can instantiate itself).
-- The one missing ingredient, deciding every proposition, is the hypothesis `em`.
-- Goal: loop_from_em : ((Q : *) -> Q or Not Q) -> Void

def Not (A : *) : * = A -> Void;

def Two : * = Unit or Unit;
def tt : Two = inl ();
def ff : Two = inr ();

-- large elimination of the *-sum: Two -> *
def El (b : Two) : * = either_rect Unit Unit (\_. *) (\_. Unit) (\_. Void) b;

def Pw (A : *) : * = A -> Two;

def U2 : * = (X : *) -> (Pw (Pw X) -> X) -> Pw (Pw X);

def tau2 (t : Pw (Pw U2)) : U2 = \X f p. t (\x. p (f (x X f)));

def sigma2 (s : U2) : Pw (Pw U2) = s U2 (\t. tau2 t);

-- decide a proposition, using em
def down (em : (Q : *) -> Q or Not Q) (Q : *) : Two =
  either_rect Q (Not Q) (\_. Two) (\_. tt) (\_. ff) (em Q);

-- El (down Q) <-> Q, by cases on em Q
def toE (em : (Q : *) -> Q or Not Q) (Q : *) (q : Q) : El (down em Q) =
  either_rect Q (Not Q)
    (\e. El (either_rect Q (Not Q) (\_. Two) (\_. tt) (\_. ff) e))
    (\a. ())
    (\n. n q)
    (em Q);

def fromE (em : (Q : *) -> Q or Not Q) (Q : *) (r : El (down em Q)) : Q =
  either_rect Q (Not Q)
    (\e. El (either_rect Q (Not Q) (\_. Two) (\_. tt) (\_. ff) e) -> Q)
    (\a _. a)
    (\n r2. absurd Q r2)
    (em Q) r;

def Dd (y : U2) : * =
  (p : Pw U2) -> El (sigma2 y p) -> El (p (tau2 (sigma2 y)));

def Delta2 (em : (Q : *) -> Q or Not Q) : Pw U2 = \y. down em (Not (Dd y));

def Omega2 (em : (Q : *) -> Q or Not Q) : U2 =
  tau2 (\p. down em ((x : U2) -> El (sigma2 x p) -> El (p x)));

def lem1 (em : (Q : *) -> Q or Not Q) (p : Pw U2)
         (H1 : (x : U2) -> El (sigma2 x p) -> El (p x)) : El (p (Omega2 em)) =
  H1 (Omega2 em)
     (toE em ((x : U2) -> El (sigma2 x (\y. p (tau2 (sigma2 y)))) -> El (p (tau2 (sigma2 x))))
             (\x. H1 (tau2 (sigma2 x))));

def lem2 (em : (Q : *) -> Q or Not Q) : Not (Dd (Omega2 em)) =
  fromE em (Not (Dd (Omega2 em)))
    (lem1 em (Delta2 em)
      (\x H2. toE em (Not (Dd x))
        (\H3. fromE em (Not (Dd (tau2 (sigma2 x)))) (H3 (Delta2 em) H2)
                (\p. H3 (\y. p (tau2 (sigma2 y)))))));

def lem3 (em : (Q : *) -> Q or Not Q) : Dd (Omega2 em) =
  \p H1. lem1 em (\y. p (tau2 (sigma2 y)))
           (fromE em ((x : U2) -> El (sigma2 x (\y. p (tau2 (sigma2 y)))) -> El (p (tau2 (sigma2 x)))) H1);

def loop_from_em (em : (Q : *) -> Q or Not Q) : Void = lem2 em (lem3 em);
