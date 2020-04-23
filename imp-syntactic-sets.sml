datatype Nat = Succ of Nat | Zero

datatype T = True | False

datatype Loc = Location of int

datatype Aexp
 = ANumber of Nat
 | ALocation of Loc
 | AAdd of (Aexp * Aexp)
 | ASubtract of (Aexp * Aexp)
 | AMultiply of (Aexp * Aexp)

datatype Bexp
 = BTruthValue of T
 | BEq of (Aexp * Aexp)
 | BLeq of (Aexp * Aexp)
 | BNot of Bexp
 | BAnd of (Bexp * Bexp)
 | BOr of (Bexp * Bexp)

datatype Com
 = Skip
 | Assign of (Loc * Aexp)
 | Sequence of (Com * Com)
 | IfThenElse of (Bexp * Com * Com)
 | WhileDo of (Bexp * Com)


datatype IMPexp
 = Nat of Nat
 | T of T
 | Loc of Loc
 | Aexp of Aexp
 | Bexp of Bexp
 | Com of Com


fun identNat (pair: Nat * Nat): bool =
  case pair of
     (Zero, Zero) => true
   | (Zero, Succ _) => false
   | (Succ _, Zero) => false
   | (Succ a, Succ b) => identNat (a, b)


fun identT (pair: T * T): bool =
  case pair of
     (True, False) => false
   | (False, True) => false
   | _ => true


fun identLoc (pair: Loc * Loc): bool =
  case pair of
     (Location k, Location m) => k = m

fun identAexp (pair: Aexp * Aexp): bool =
  case pair of
     (ANumber n0, ANumber n1) => identNat(n0, n1)
   | (ALocation l0, ALocation l1) => identLoc(l0, l1)
   | (AAdd (a0, a1), AAdd (b0, b1)) => a0 = b0 andalso a1 = b1
   | (ASubtract (a0, a1), ASubtract (b0, b1)) => a0 = b0 andalso a1 = b1
   | (AMultiply (a0, a1), AMultiply (b0, b1)) => a0 = b0 andalso a1 = b1


val add1: Aexp = AAdd (ANumber (Succ (Succ Zero)), ANumber (Succ Zero))
val add2: Aexp = AAdd (ANumber (Succ Zero), ANumber (Succ (Succ Zero)))

val add1Ident = identAexp(add1, add2)
