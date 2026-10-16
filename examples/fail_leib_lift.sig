-- Must FAIL, each independently.
-- Small proofs do not ascribe to large types: conversion is equality, so a
-- `*`-motive proof never converts to a `Type0`-motive one (that would be
-- large elimination through the back door).
def path : (T:*) -> (a:T) -> (b:T) -> * = \T a b. (P:(T -> *)) -> (P a) -> (P b);
def liftPath : (T:*) -> (a:T) -> path T a a -> (P:(T -> Type0)) -> P a -> P a = \T a p. p;
def Q : * = Quot Unit (\_ _. Unit);
def liftSound : (a:Unit) -> (b:Unit) -> (h:Unit) -> (Q2:(Q -> Type0)) -> Q2 (quot_mk a) -> Q2 (quot_mk b) = \a b h. quot_sound Unit (\_ _. Unit) a b h;
