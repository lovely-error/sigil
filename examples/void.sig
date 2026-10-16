-- Empty type and explosion (`absurd : (A:*) -> Void -> A`, primitive).
-- With Void, consistency is sharply statable: a closed term of Void would be
-- a paradox. None exists by construction (no constructors; `absurd`
-- applications stay stuck-neutral, so evaluation can never manufacture one).
-- Explosion targets `*`-types only (`#`-motives are inexpressible: `#` is
-- unquantifiable — the same structural reason as `path`'s motives).

-- Ex falso quodlibet.
def exfalso : (A:*) -> Void -> A = \A v. absurd A v;

-- `absurd` at `Void` itself.
def absurdVoid : (v:Void) -> Void = \v. absurd Void v;

-- Explosion at higher small types (`T -> T` lives in `*`).
def boom : (v:Void) -> (T:*) -> T -> T = \v T. absurd (T -> T) v;
