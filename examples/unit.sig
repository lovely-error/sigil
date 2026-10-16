-- One-element type with sole value `()`, eliminated by `unit_rect`.
-- Closed inhabitants of sums at last: `inl ()`, `inr ()`.

def unitVal : Unit = ();
def rectDemo : (P:(Unit -> *)) -> (b:P ()) -> (u:Unit) -> P u
  = \P b u. unit_rect P b u;

-- First closed sum computation: case on `inl ()` / `inr ()`.
def pickLeft : (Unit or Unit) -> Unit
  = \e. either_rect Unit Unit (\_. Unit) (\_. ()) (\_. ()) e;
def leftIsUnit : Unit = pickLeft (inl ());
def rightIsUnit : Unit = pickLeft (inr ());
