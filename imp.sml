datatype Nat = Succ of Nat | Zero

datatype Sign = Positive | Negative

datatype N = Number of (Sign * Nat)

datatype SizeComparison = SizeGT | SizeLT | SizeEQ

fun addNat (pair: Nat * Nat) =
  case pair of
     (Zero, n) => n
   | (n, Zero) => n
   | (Succ m, n) => addNat(m, Succ (Succ n))

fun cancelNats (pair: Nat * Nat): (SizeComparison * Nat) =
  case pair of
     (Zero, Zero) => (SizeEQ, Zero)
   | (Zero, n) => (SizeLT, n)
   | (n, Zero) => (SizeGT, n)
   | (Succ m, Succ n) => cancelNats(m,n)


fun computeAddForPosNeg (pair: SizeComparison * Nat): N =
  case pair of
     (SizeEQ, _) => Number (Positive, Zero)
   | (SizeLT, r) => Number (Negative, r)
   | (SizeGT, r) => Number (Positive, r)

fun addN (pair: N * N): N =
  case pair of
     (Number (Positive, m), Number (Positive, n)) => Number (Positive, addNat(m, n))
   | (Number (Negative, m), Number (Negative, n)) => Number (Negative, addNat(m, n))
   | (Number (Positive, m), Number (Negative, n)) => computeAddForPosNeg (cancelNats(m, n))
   | (Number (Negative, m), Number (Positive, n)) => computeAddForPosNeg (cancelNats(n, m))





datatype T = True | False

datatype Loc = Location of int

datatype Aexp
 = ANumber of N
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
 = N of N
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


fun identN (pair: N * N): bool =
  case pair of
     (Number (Positive, _), Number (Negative, _)) => false
   | (Number (Negative, _), Number (Positive, _)) => false
   | (Number (Positive, m), Number (Positive, n)) => identNat(m, n)
   | (Number (Negative, m), Number (Negative, n)) => identNat(m, n)


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
     (ANumber n0, ANumber n1) => identN(n0, n1)
   | (ALocation l0, ALocation l1) => identLoc(l0, l1)
   | (AAdd (a0, a1), AAdd (b0, b1)) => a0 = b0 andalso a1 = b1
   | (ASubtract (a0, a1), ASubtract (b0, b1)) => a0 = b0 andalso a1 = b1
   | (AMultiply (a0, a1), AMultiply (b0, b1)) => a0 = b0 andalso a1 = b1


fun evalAexp (pair: Aexp * (Loc -> N)) : N =
  let val a = #1 pair
      val st = #2 pair
  in
    case a of
       ANumber n => n
     | ALocation l => st(l)
     | AAdd (a0, a1) => addN(evalAexp(a0, st), evalAexp(a1, st))
     | ASubtract (a0, a1) => raise Fail "this isn't implemented yet"
     | AMultiply (a0, a1) => raise Fail "this isn't implemented yet"
  end




(* demos *)
val add1: Aexp = AAdd (
  ANumber (Number (Positive, (Succ (Succ Zero)))),
  ANumber (Number (Positive, (Succ Zero)))
)

val add2: Aexp = AAdd (
  ANumber (Number (Positive, (Succ Zero))),
  ANumber (Number (Positive, (Succ (Succ Zero))))
)

val add1Ident = identAexp(add1, add2)


val stateAllZeros: Loc -> N = fn l => Number (Positive, Zero);
