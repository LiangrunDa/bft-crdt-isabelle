object BFT_ORSet {

def list_all[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

abstract sealed class set[A]
final case class seta[A](a : List[A]) extends set[A]
final case class coset[A](a : List[A]) extends set[A]

trait equal[A] {
  val `BFT_ORSet.equal` : (A, A) => Boolean
}
def equal[A](a : A, b : A)(implicit A: equal[A]) : Boolean =
  A.`BFT_ORSet.equal`(a, b)
object equal {
  implicit def `BFT_ORSet.equal_operation` : equal[operation] = new
    equal[operation] {
    val `BFT_ORSet.equal` = (a : operation, b : operation) =>
      equal_operationa(a, b)
  }
  implicit def `BFT_ORSet.equal_prod`[A : equal, B : equal] : equal[(A, B)] =
    new equal[(A, B)] {
    val `BFT_ORSet.equal` = (a : (A, B), b : (A, B)) => equal_proda[A, B](a, b)
  }
  implicit def `BFT_ORSet.equal_literal` : equal[String] = new equal[String] {
    val `BFT_ORSet.equal` = (a : String, b : String) => a == b
  }
  implicit def `BFT_ORSet.equal_fset`[A : equal] : equal[fset[A]] = new
    equal[fset[A]] {
    val `BFT_ORSet.equal` = (a : fset[A], b : fset[A]) => equal_fseta[A](a, b)
  }
}

def eq[A : equal](a : A, b : A) : Boolean = equal[A](a, b)

def membera[A : equal](x0 : List[A], y : A) : Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def member[A : equal](x : A, xa1 : set[A]) : Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def less_eq_set[A : equal](a : set[A], b : set[A]) : Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => list_all[A](((y : A) => ! (member[A](y, a))), ys)
  case (seta(xs), b) => list_all[A](((x : A) => member[A](x, b)), xs)
}

abstract sealed class fset[A]
final case class Abs_fset[A](a : set[A]) extends fset[A]

def fset[A](x0 : fset[A]) : set[A] = x0 match {
  case Abs_fset(x) => x
}

def less_eq_fset[A : equal](xa : fset[A], xc : fset[A]) : Boolean =
  less_eq_set[A](fset[A](xa), fset[A](xc))

def equal_fseta[A : equal](a : fset[A], b : fset[A]) : Boolean =
  less_eq_fset[A](a, b) && less_eq_fset[A](b, a)

def equal_proda[A : equal, B : equal](x0 : (A, B), x1 : (A, B)) : Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

abstract sealed class operation
final case class Increment() extends operation
final case class Decrement() extends operation

def equal_operationa(x0 : operation, x1 : operation) : Boolean = (x0, x1) match
  {
  case (Increment(), Decrement()) => false
  case (Decrement(), Increment()) => false
  case (Decrement(), Decrement()) => true
  case (Increment(), Increment()) => true
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a : num) extends num
final case class Bit1(a : num) extends num

abstract sealed class int
final case class zero_int() extends int
final case class Pos(a : num) extends int
final case class Neg(a : num) extends int

def dup(x0 : int) : int = x0 match {
  case Neg(n) => Neg(Bit0(n))
  case Pos(n) => Pos(Bit0(n))
  case zero_int() => zero_int()
}

def uminus_int(x0 : int) : int = x0 match {
  case Neg(m) => Pos(m)
  case Pos(m) => Neg(m)
  case zero_int() => zero_int()
}

def plus_num(x0 : num, x1 : num) : num = (x0, x1) match {
  case (Bit1(m), Bit1(n)) => Bit0(plus_num(plus_num(m, n), One()))
  case (Bit1(m), Bit0(n)) => Bit1(plus_num(m, n))
  case (Bit1(m), One()) => Bit0(plus_num(m, One()))
  case (Bit0(m), Bit1(n)) => Bit1(plus_num(m, n))
  case (Bit0(m), Bit0(n)) => Bit0(plus_num(m, n))
  case (Bit0(m), One()) => Bit1(m)
  case (One(), Bit1(n)) => Bit0(plus_num(n, One()))
  case (One(), Bit0(n)) => Bit1(n)
  case (One(), One()) => Bit0(One())
}

def one_int : int = Pos(One())

def BitM(x0 : num) : num = x0 match {
  case One() => One()
  case Bit0(n) => Bit1(BitM(n))
  case Bit1(n) => Bit1(Bit0(n))
}

def minus_int(k : int, l : int) : int = (k, l) match {
  case (Neg(m), Neg(n)) => sub(n, m)
  case (Neg(m), Pos(n)) => Neg(plus_num(m, n))
  case (Pos(m), Neg(n)) => Pos(plus_num(m, n))
  case (Pos(m), Pos(n)) => sub(m, n)
  case (zero_int(), l) => uminus_int(l)
  case (k, zero_int()) => k
}

def plus_int(k : int, l : int) : int = (k, l) match {
  case (Neg(m), Neg(n)) => Neg(plus_num(m, n))
  case (Neg(m), Pos(n)) => sub(n, m)
  case (Pos(m), Neg(n)) => sub(m, n)
  case (Pos(m), Pos(n)) => Pos(plus_num(m, n))
  case (zero_int(), l) => l
  case (k, zero_int()) => k
}

def sub(x0 : num, x1 : num) : int = (x0, x1) match {
  case (Bit0(m), Bit1(n)) => minus_int(dup(sub(m, n)), one_int)
  case (Bit1(m), Bit0(n)) => plus_int(dup(sub(m, n)), one_int)
  case (Bit1(m), Bit1(n)) => dup(sub(m, n))
  case (Bit0(m), Bit0(n)) => dup(sub(m, n))
  case (One(), Bit1(n)) => Neg(Bit0(n))
  case (One(), Bit0(n)) => Neg(BitM(n))
  case (Bit1(m), One()) => Pos(Bit0(m))
  case (Bit0(m), One()) => Pos(BitM(m))
  case (One(), One()) => zero_int()
}

def list_ex[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def Bex[A](x0 : set[A], p : A => Boolean) : Boolean = (x0, p) match {
  case (seta(xs), p) => list_ex[A](p, xs)
}

def Ball[A](x0 : set[A], p : A => Boolean) : Boolean = (x0, p) match {
  case (seta(xs), p) => list_all[A](p, xs)
}

def fold[A, B](f : A => B => B, x1 : List[A], s : B) : B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def removeAll[A : equal](x : A, xa1 : List[A]) : List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def inserta[A : equal](x : A, xs : List[A]) : List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x : A, xa1 : set[A]) : set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def filter[A](p : A => Boolean, x1 : List[A]) : List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def finsert[A : equal](xb : A, xc : fset[A]) : fset[A] =
  Abs_fset[A](insert[A](xb, fset[A](xc)))

def counter_op(xa0 : operation, x : int) : Option[int] = (xa0, x) match {
  case (Increment(), x) => Some[int](plus_int(x, one_int))
  case (Decrement(), x) => Some[int](minus_int(x, one_int))
}

def bot_set[A] : set[A] = seta[A](Nil)

def sup_set[A : equal](x0 : set[A], a : set[A]) : set[A] = (x0, a) match {
  case (coset(xs), a) =>
    coset[A](filter[A](((x : A) => ! (member[A](x, a))), xs))
  case (seta(xs), a) =>
    fold[A, set[A]](((aa : A) => (b : set[A]) => insert[A](aa, b)), xs, a)
}

def is_valid[A, B](semF : (fset[(fset[A], B)]) => ((fset[A], B)) => Boolean,
                    strF : (fset[(fset[A], B)]) => ((fset[A], B)) => Boolean,
                    g : fset[(fset[A], B)], x : (fset[A], B)) : Boolean
  =
  (semF(g))(x) && (strF(g))(x)

def interpret_op[A](uu : ((fset[A], operation)) => A, x1 : (fset[A], operation),
                     s : int) : Option[int]
  =
  (uu, x1, s) match {
  case (uu, (uv, oper), s) => counter_op(oper, s)
}

def bot_fset[A] : fset[A] = Abs_fset[A](bot_set[A])

def sup_fset[A : equal](xb : fset[A], xc : fset[A]) : fset[A] =
  Abs_fset[A](sup_set[A](fset[A](xb), fset[A](xc)))

def is_struct_valid[A : equal,
                     B : equal](h : ((fset[A], B)) => A, g : fset[(fset[A], B)],
                                 x2 : (fset[A], B)) : Boolean
  =
  (h, g, x2) match {
  case (h, g, (hashes, vala)) =>
    Ball[A](fset[A](hashes),
             ((ha : A) =>
               Bex[(fset[A],
                     B)](fset[(fset[A], B)](g),
                          ((n : (fset[A], B)) => eq[A](h(n), ha))))) &&
      (! (member[(fset[A], B)]((hashes, vala), fset[(fset[A], B)](g))) &&
        ! (member[A](h((hashes, vala)), fset[A](hashes))))
}

def check_and_apply[A : equal,
                     B : equal](semF : (fset[(fset[A], B)]) =>
 ((fset[A], B)) => Boolean,
                                 strF : (fset[(fset[A], B)]) =>
  ((fset[A], B)) => Boolean,
                                 x2 : (List[(fset[A], B)], fset[(fset[A], B)]),
                                 n : (fset[A],
                                       B)) : (List[(fset[A], B)],
       fset[(fset[A], B)])
  =
  (semF, strF, x2, n) match {
  case (semF, strF, (ah, g), n) =>
    (if (is_valid[A, B](semF, strF, g, n))
      (ah ++ List(n),
        sup_fset[(fset[A],
                   B)](g, finsert[(fset[A], B)](n, bot_fset[(fset[A], B)])))
      else (ah, g))
}

def is_counter_sem_valid[A](uu : ((fset[A], operation)) =>
                                   ((fset[A], operation)) => Boolean,
                             uv : ((fset[A], operation)) => A,
                             uw : set[(fset[A], operation)],
                             ux : (fset[A], operation)) : Boolean
  =
  true

def counter_is_struct_valid_impl : (((fset[String], operation)) => String) =>
                                     (fset[(fset[String], operation)]) =>
                                       ((fset[String], operation)) => Boolean
  =
  ((a : ((fset[String], operation)) => String) =>
    (b : fset[(fset[String], operation)]) => (c : (fset[String], operation)) =>
    is_struct_valid[String, operation](a, b, c))

def is_counter_sem_valid_impl : (((fset[String], operation)) =>
                                  ((fset[String], operation)) => Boolean) =>
                                  (((fset[String], operation)) => String) =>
                                    (set[(fset[String], operation)]) =>
                                      ((fset[String], operation)) => Boolean
  =
  ((a : ((fset[String], operation)) => ((fset[String], operation)) => Boolean)
     =>
    (b : ((fset[String], operation)) => String) =>
    (c : set[(fset[String], operation)]) => (d : (fset[String], operation)) =>
    is_counter_sem_valid[String](a, b, c, d))

def counter_check_and_apply(c : (fset[(fset[String], operation)]) =>
                                  ((fset[String], operation)) =>
                                    ((fset[String], operation)) => Boolean,
                             h : ((fset[String], operation)) =>
                                   String) : ((List[(fset[String], operation)],
       fset[(fset[String], operation)])) =>
       ((fset[String], operation)) =>
         (List[(fset[String], operation)], fset[(fset[String], operation)])
  =
  ((a : (List[(fset[String], operation)], fset[(fset[String], operation)])) =>
    (b : (fset[String], operation)) =>
    check_and_apply[String,
                     operation](((g : fset[(fset[String], operation)]) =>
                                  is_counter_sem_valid_impl.apply(c(g)).apply(h).apply(fset[(fset[String],
              operation)](g))),
                                 counter_is_struct_valid_impl.apply(h), a, b))

def counter_interpret_op_impl : (((fset[String], operation)) => String) =>
                                  ((fset[String], operation)) =>
                                    int => Option[int]
  =
  ((a : ((fset[String], operation)) => String) =>
    (b : (fset[String], operation)) => (c : int) =>
    interpret_op[String](a, b, c))

} /* object BFT_ORSet */
