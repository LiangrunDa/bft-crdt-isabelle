object BFT_ORSet {

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a : nat) extends nat

def equal_nata(x0 : nat, x1 : nat) : Boolean = (x0, x1) match {
  case (zero_nat(), Suc(x2)) => false
  case (Suc(x2), zero_nat()) => false
  case (Suc(x2), Suc(y2)) => equal_nata(x2, y2)
  case (zero_nat(), zero_nat()) => true
}

trait equal[A] {
  val `BFT_ORSet.equal` : (A, A) => Boolean
}
def equal[A](a : A, b : A)(implicit A: equal[A]) : Boolean =
  A.`BFT_ORSet.equal`(a, b)
object equal {
  implicit def
    `BFT_ORSet.equal_operation`[A : equal, B : equal] : equal[operation[A, B]] =
    new equal[operation[A, B]] {
    val `BFT_ORSet.equal` = (a : operation[A, B], b : operation[A, B]) =>
      equal_operationa[A, B](a, b)
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
  implicit def `BFT_ORSet.equal_set`[A : equal] : equal[set[A]] = new
    equal[set[A]] {
    val `BFT_ORSet.equal` = (a : set[A], b : set[A]) => equal_seta[A](a, b)
  }
  implicit def `BFT_ORSet.equal_nat` : equal[nat] = new equal[nat] {
    val `BFT_ORSet.equal` = (a : nat, b : nat) => equal_nata(a, b)
  }
}

def list_all[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

abstract sealed class set[A]
final case class seta[A](a : List[A]) extends set[A]
final case class coset[A](a : List[A]) extends set[A]

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

def equal_seta[A : equal](a : set[A], b : set[A]) : Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

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

abstract sealed class operation[A, B]
final case class Add[B, A](a : B) extends operation[A, B]
final case class Rem[A, B](a : set[A], b : B) extends operation[A, B]

def equal_operationa[A : equal,
                      B : equal](x0 : operation[A, B],
                                  x1 : operation[A, B]) : Boolean
  =
  (x0, x1) match {
  case (Add(x1), Rem(x21, x22)) => false
  case (Rem(x21, x22), Add(x1)) => false
  case (Rem(x21, x22), Rem(y21, y22)) => eq[set[A]](x21, y21) && eq[B](x22, y22)
  case (Add(x1), Add(y1)) => eq[B](x1, y1)
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

def remove[A : equal](x : A, xa1 : set[A]) : set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](inserta[A](x, xs))
  case (x, seta(xs)) => seta[A](removeAll[A](x, xs))
}

def fun_upd[A : equal, B](f : A => B, a : A, b : B) : A => B =
  ((x : A) => (if (eq[A](x, a)) b else f(x)))

def filter[A](p : A => Boolean, x1 : List[A]) : List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def finsert[A : equal](xb : A, xc : fset[A]) : fset[A] =
  Abs_fset[A](insert[A](xb, fset[A](xc)))

def op_elem[A, B](oper : operation[A, B]) : B = (oper match {
           case Add(e) => e
           case Rem(_, e) => e
         })

def bot_set[A] : set[A] = seta[A](Nil)

def init_state[A, B] : A => set[B] = ((_ : A) => bot_set[B])

def snd[A, B](x0 : (A, B)) : B = x0 match {
  case (x1, x2) => x2
}

def minus_set[A : equal](a : set[A], x1 : set[A]) : set[A] = (a, x1) match {
  case (a, coset(xs)) => seta[A](filter[A](((x : A) => member[A](x, a)), xs))
  case (a, seta(xs)) =>
    fold[A, set[A]](((aa : A) => (b : set[A]) => remove[A](aa, b)), xs, a)
}

def sup_set[A : equal](x0 : set[A], a : set[A]) : set[A] = (x0, a) match {
  case (coset(xs), a) =>
    coset[A](filter[A](((x : A) => ! (member[A](x, a))), xs))
  case (seta(xs), a) =>
    fold[A, set[A]](((aa : A) => (b : set[A]) => insert[A](aa, b)), xs, a)
}

def interpret_op[A : equal,
                  B : equal](h : ((fset[A], operation[A, B])) => A,
                              x1 : (fset[A], operation[A, B]),
                              state : B => set[A]) : Option[B => set[A]]
  =
  (h, x1, state) match {
  case (h, (hs, oper), state) =>
    {
      val before = state(op_elem[A, B](oper)) : (set[A])
      val after =
        (oper match {
           case Add(_) =>
             sup_set[A](before, insert[A](h((hs, oper)), bot_set[A]))
           case Rem(is, _) => minus_set[A](before, is)
         }) : (set[A]);
      Some[B => set[A]](fun_upd[B, set[A]](state, op_elem[A, B](oper), after))
    }
}

def is_valid[A, B](semF : (fset[(fset[A], B)]) => ((fset[A], B)) => Boolean,
                    strF : (fset[(fset[A], B)]) => ((fset[A], B)) => Boolean,
                    g : fset[(fset[A], B)], x : (fset[A], B)) : Boolean
  =
  (semF(g))(x) && (strF(g))(x)

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

def is_orset_sem_valid[A : equal,
                        B : equal](c : ((fset[A], operation[A, B])) =>
 ((fset[A], operation[A, B])) => Boolean,
                                    h : ((fset[A], operation[A, B])) => A,
                                    s : set[(fset[A], operation[A, B])],
                                    x3 : (fset[A], operation[A, B])) : Boolean
  =
  (c, h, s, x3) match {
  case (c, h, s, (hs, Add(e))) => true
  case (c, h, s, (hs, Rem(is, e))) =>
    Ball[A](is, ((i : A) =>
                  Bex[(fset[A],
                        operation[A, B])](s,
   ((n : (fset[A], operation[A, B])) =>
     (c(n))((hs, Rem[A, B](is, e))) &&
       (equal_operationa[A, B](snd[fset[A], operation[A, B]](n),
                                Add[B, A](e)) &&
         eq[A](h(n), i))))))
}

def is_orset_sem_valid_nat : (((fset[String], operation[String, nat])) =>
                               ((fset[String], operation[String, nat])) =>
                                 Boolean) =>
                               (((fset[String], operation[String, nat])) =>
                                 String) =>
                                 (set[(fset[String],
operation[String, nat])]) =>
                                   ((fset[String], operation[String, nat])) =>
                                     Boolean
  =
  ((a : ((fset[String], operation[String, nat])) =>
          ((fset[String], operation[String, nat])) => Boolean)
     =>
    (b : ((fset[String], operation[String, nat])) => String) =>
    (c : set[(fset[String], operation[String, nat])]) =>
    (d : (fset[String], operation[String, nat])) =>
    is_orset_sem_valid[String, nat](a, b, c, d))

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

def orset_is_struct_valid : (((fset[String], operation[String, nat])) =>
                              String) =>
                              (fset[(fset[String], operation[String, nat])]) =>
                                ((fset[String], operation[String, nat])) =>
                                  Boolean
  =
  ((a : ((fset[String], operation[String, nat])) => String) =>
    (b : fset[(fset[String], operation[String, nat])]) =>
    (c : (fset[String], operation[String, nat])) =>
    is_struct_valid[String, operation[String, nat]](a, b, c))

def orset_check_and_apply(c : (fset[(fset[String], operation[String, nat])]) =>
                                ((fset[String], operation[String, nat])) =>
                                  ((fset[String], operation[String, nat])) =>
                                    Boolean,
                           h : ((fset[String], operation[String, nat])) =>
                                 String) : ((List[(fset[String],
            operation[String, nat])],
     fset[(fset[String], operation[String, nat])])) =>
     ((fset[String], operation[String, nat])) =>
       (List[(fset[String], operation[String, nat])],
         fset[(fset[String], operation[String, nat])])
  =
  ((a : (List[(fset[String], operation[String, nat])],
          fset[(fset[String], operation[String, nat])]))
     =>
    (b : (fset[String], operation[String, nat])) =>
    check_and_apply[String,
                     operation[String,
                                nat]](((g : fset[(fset[String],
           operation[String, nat])])
 =>
is_orset_sem_valid_nat.apply(c(g)).apply(h).apply(fset[(fset[String],
                 operation[String, nat])](g))),
                                       orset_is_struct_valid.apply(h), a, b))

def orset_interpret_op_nat : (((fset[String], operation[String, nat])) =>
                               String) =>
                               ((fset[String], operation[String, nat])) =>
                                 (nat => set[String]) =>
                                   Option[nat => set[String]]
  =
  ((a : ((fset[String], operation[String, nat])) => String) =>
    (b : (fset[String], operation[String, nat])) => (c : nat => set[String]) =>
    interpret_op[String, nat](a, b, c))

} /* object BFT_ORSet */
