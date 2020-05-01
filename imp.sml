datatype Nat = Succ of Nat | Zero

datatype Sign = Positive | Negative

datatype N = Number of (Sign * Nat)

datatype SizeComparison = SizeGT | SizeLT | SizeEQ

fun addNat (pair: Nat * Nat) =
  case pair of
     (Zero, n) => n
   | (n, Zero) => n
   | (Succ m, n) => addNat(m, Succ n)

fun multNat (pair: Nat * Nat) =
  case pair of
     (Zero, n) => Zero
   | (n, Zero) => Zero
   | (Succ m, n) => addNat(multNat(m, n), n)


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

fun negateN (num: N): N =
  case num of
     Number (Positive, n) => Number (Negative, n)
   | Number (Negative, n) => Number (Positive, n)

fun recNumToInt (num: N, sum: int): int =
  case num of
     Number (_, Zero) => sum
   | Number (Positive, Succ n) => recNumToInt(Number (Positive, n), sum + 1)
   | Number (Negative, Succ n) => recNumToInt(Number (Negative, n), sum - 1)

fun numToInt (num: N): int =
  recNumToInt(num, 0)


fun addN (pair: N * N): N =
  case pair of
     (Number (Positive, m), Number (Positive, n)) => Number (Positive, addNat(m, n))
   | (Number (Negative, m), Number (Negative, n)) => Number (Negative, addNat(m, n))
   | (Number (Positive, m), Number (Negative, n)) => computeAddForPosNeg (cancelNats(m, n))
   | (Number (Negative, m), Number (Positive, n)) => computeAddForPosNeg (cancelNats(n, m))

fun subN (pair: N * N): N =
  addN (#1 pair, negateN (#2 pair))


fun multN (pair: N * N): N =
  case pair of
     (Number (_, Zero), _) => Number (Positive, Zero)
   | (_, Number (_, Zero)) => Number (Positive, Zero)
   | (Number (Positive, m), Number (Positive, n)) => Number (Positive, multNat(m, n))
   | (Number (Negative, m), Number (Negative, n)) => Number (Positive, multNat(m, n))
   | (Number (Positive, m), Number (Negative, n)) => Number (Negative, multNat(m, n))
   | (Number (Negative, m), Number (Positive, n)) => Number (Negative, multNat(m, n))


datatype T = True | False

fun notT (x: T) : T =
  case x of
     True => False
   | False => True

fun andT (pair: T * T) : T =
  case pair of
     (True, True) => True
   | _ => False

fun orT (pair: T * T) : T =
  case pair of
     (False, False) => False
   | _ => True


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
   | (AAdd (a0, a1), AAdd (b0, b1)) => identAexp(a0, b0) andalso identAexp(a1, b1)
   | (ASubtract (a0, a1), ASubtract (b0, b1)) => identAexp(a0, b0) andalso identAexp(a1, b1)
   | (AMultiply (a0, a1), AMultiply (b0, b1)) => identAexp(a0, b0) andalso identAexp(a1, b1)


fun identBexp (pair: Bexp * Bexp): bool =
  case pair of
     (BTruthValue t0, BTruthValue t1) => t0 = t1
   | (BEq (a0, a1), BEq (b0, b1)) => identAexp(a0, b0) andalso identAexp(a1, b1)
   | (BLeq (a0, a1), BLeq (b0, b1)) => identAexp(a0, b0) andalso identAexp(a1, b1)
   | (BNot a0, BNot b0) => identBexp(a0, b0)
   | (BAnd (a0, a1), BAnd (b0, b1)) => identBexp(a0, b0) andalso identBexp(a1, b1)
   | (BOr (a0, a1), BOr (b0, b1)) => identBexp(a0, b0) andalso identBexp(a1, b1)


type State = Loc -> N

fun evalAexp (pair: Aexp * State) : N =
  let val a = #1 pair
      val st = #2 pair
  in
    case a of
       ANumber n => n
     | ALocation l => st(l)
     | AAdd (a0, a1) => addN(evalAexp(a0, st), evalAexp(a1, st))
     | ASubtract (a0, a1) => subN(evalAexp(a0, st), evalAexp(a1, st))
     | AMultiply (a0, a1) => multN(evalAexp(a0, st), evalAexp(a1, st))
  end


fun evalBexp (pair: Bexp * State) : T =
  let val b = #1 pair
      val st = #2 pair
  in
    case b of
       BTruthValue t => t
     | BEq (b0, b1) => if evalAexp (b0, st) = (evalAexp (b1, st)) then True else False
     | BLeq (b0, b1) => if numToInt(evalAexp (b0, st)) <= numToInt(evalAexp (b1, st)) then True else False
     | BNot b => notT (evalBexp (b, st))
     | BAnd (b0, b1) => andT (evalBexp (b0, st), evalBexp (b1, st))
     | BOr (b0, b1) => orT (evalBexp (b0, st), evalBexp (b1, st))
  end

fun evalCom (pair: Com * State) : State =
  let val c = #1 pair
      val st = #2 pair
  in
    case c of
       Skip => st
     | Assign (loc, a) => (fn l => if l = loc then evalAexp (a, st) else (st l))
     | Sequence (c0, c1) => let val st' = evalCom (c0, st)
                            in evalCom (c1, st')
                            end
     | IfThenElse (b, c0, c1) => let val t = evalBexp (b, st)
                                 in if t = True then evalCom (c0, st) else evalCom (c1, st)
                                 end
     | WhileDo (b, c0) => let val t = evalBexp (b, st)
                          in if t = False then st else evalCom (c, evalCom (c0, st))
                          end
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


val stateAllZeros: State = fn l => Number (Positive, Zero);


val one: Nat = Succ Zero;
val two: Nat = Succ one;
val three: Nat = Succ two;
val four: Nat = Succ three;
val posOne: N = Number (Positive, one);
val posTwo: N = Number (Positive, two);
val posThree: N = Number (Positive, three);
val negOne: N = Number (Negative, one);
val negFour: N = Number (Negative, four);

val expAdd: Aexp = AAdd (ANumber posOne, ANumber posTwo);
val expAddResult: N = evalAexp(expAdd, stateAllZeros);

val addResultInt: int = numToInt(expAddResult);


val expSub: Aexp = ASubtract (ANumber negOne, ANumber posThree);
val expSubResult: N = evalAexp(expSub, stateAllZeros);

val subResultInt: int = numToInt(expSubResult);


val expMult: Aexp = AMultiply (ANumber negFour, ANumber posTwo);
val expMultResult: N = evalAexp(expMult, stateAllZeros);
val multResultInt: int = numToInt(expMultResult);


val expEq: Bexp = BEq (add1, add2)
val expEqResult: T = evalBexp(expEq, stateAllZeros)

val expLeq: Bexp = BLeq (ANumber posThree, ANumber posOne)
val expLeqResult: T = evalBexp(expLeq, stateAllZeros)


val comAssign: Com = Assign (Location 5, expAdd)
val comAssignResult : State = evalCom (comAssign, stateAllZeros)
val comAssignResult4 = numToInt(comAssignResult (Location 4))
val comAssignResult5 = numToInt(comAssignResult (Location 5))
