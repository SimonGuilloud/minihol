import Core._
import Theorems._
import PrettyPrinter._
import Sugar._
import Helper._
import Deduction._

object BasicConstants {

  val BooleanOp: HOL_type = Bool->(Bool->Bool)
  private val x = Variable("x", Bool)
  private val y = Variable("y", Bool)
  private val A = TypeVariable("A")
  private val xA = Variable("x", A)
  private val yA = Variable("y", A)
  private val r = Variable("r", Bool)
  private val s = Variable("s", Bool)
  private val ff = Variable("f", BooleanOp)
  private val PA = Variable("P", Func(A, Bool))

  //val === = safe_equal(_,_)
  val <=> = equal.substituteType(A, Bool)

  val top = Constant("T", Bool)
  val top_def = DEFINE_CONSTANT(top, \(x, x) === \(x, x))

  val /\ = Constant("/\\", BooleanOp)
  val and_def = DEFINE_CONSTANT(/\, \(r, \(s, \(ff, ff(r)(s)) === \(ff, ff(top)(top)) )) )

  val ==> = Constant("->", BooleanOp)
  val implies_def = DEFINE_CONSTANT(==>, \(r, \(s, /\(r)(s) <=> r )) )

  val \-/ = Constant("\\-/", (A->Bool)-> Bool)
  val forall_def = DEFINE_CONSTANT(\-/, \(PA, PA === \(xA, top)) )

  val \/ = Constant("\\/", BooleanOp)
  val or_def = DEFINE_CONSTANT(\/, \(r, \(s, \-/(x, ( r ==> x ) ==> (( s ==> x ) ==> x ) ) )) )

  val bot = Constant("L", Bool)
  val bot_def = DEFINE_CONSTANT(bot, \-/(r, r))

  val ~ = Constant("~", Bool->Bool)
  val not_def = DEFINE_CONSTANT(~, \(r,r ==> bot))


  //Refining Boolean constants definition

  // |- t1/\t2 = (\g g(t1)(t2) <=> \g g(T)(T))
  def AND_THM(t1: Term, t2: Term ): Theorem = {
    require(t1.typ == Bool && t2.typ == Bool, "Types of t1 and y2 must be Bool, type of g must be Bool->Bool, g must not be free in t1 and t2")
    val r1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "r"), Bool)
    val s1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "s"), Bool)
    val ff1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "ff"), BooleanOp)

    val old_def = \(r, \(s, \(ff, ff(r)(s)) === \(ff, ff(top)(top)) ))
    val new_def = \(r1, \(s1, \(ff1, ff1(r1)(s1)) === \(ff1, ff1(top)(top)) ))
    val thm_and_renamed = TRANS(and_def, ALPHA_EQUIVALENCE(old_def, new_def)) // /\ == new_def
    val thm1 = AP_ARG(thm_and_renamed, t1) // /\(t1) == new_def(t1)
    val thm2 = TRANS(thm1, BETA_CONV(new_def(t1)))
    val thm3 = AP_ARG(thm2, t2)
    val int_def = \(s1, \(ff1, ff1(t1)(s1)) === \(ff1, ff1(top)(top)) )
    val thm4 = _TRANS(thm3, BETA_CONV(int_def(t2)) )
    thm4
  }

  def IMP_THM(t1: Term, t2: Term ): Theorem = {
    require(t1.typ == Bool && t2.typ == Bool, "Types of t1 and y2 must be Bool")
    val r1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "r"), Bool)
    val s1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "s"), Bool)

    val old_def = \(r, \(s, /\(r)(s) <=> r ))
    val new_def = \(r1, \(s1, /\(r1)(s1) <=> r1 ))
    val thm_implies_renamed = TRANS(implies_def, ALPHA_EQUIVALENCE(old_def, new_def)) // /\ == new_def
    val thm1 = AP_ARG(thm_implies_renamed, t1) // /\(t1) == new_def(t1)
    val thm2 = TRANS(thm1, BETA_CONV(new_def(t1)))
    val thm3 = AP_ARG(thm2, t2)
    val int_def = \(s, /\(t1)(s) <=> t1 )
    val thm4 = _TRANS(thm3, BETA_CONV(int_def(t2)) )
    thm4
  }

  def OR_THM(t1: Term, t2: Term ): Theorem = {
    require(t1.typ == Bool && t2.typ == Bool, "Types of t1 and y2 must be Bool")
    val r1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "r"), Bool)
    val s1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "s"), Bool)
    val x1 = Variable(newVariable(t1.freeVariables++t2.freeVariables, "x"), Bool)

    val old_def = \(r, \(s, \-/(x, ==>( ==>(r)(x) )( ==>( ==>(s)(x) )(x) ))  ))
    val new_def = \(r1, \(s1, \-/(x1, ==>( ==>(r1)(x1) )( ==>( ==>(s1)(x1) )(x1) ))  ))
    val thm_or_renamed = TRANS(or_def, ALPHA_EQUIVALENCE(old_def, new_def)) // /\ == new_def
    val thm1 = AP_ARG(thm_or_renamed, t1) // /\(t1) == new_def(t1)
    val thm2 = TRANS(thm1, BETA_CONV(new_def(t1)))
    val thm3 = AP_ARG(thm2, t2)
    val int_def = \(s1, \-/(x1, ==>( ==>(t1)(x1) )( ==>( ==>(s1)(x1) )(x1) ))  )
    val thm4 = _TRANS(thm3, BETA_CONV(int_def(t2)) )
    thm4
  }

  def NOT_THM(t1: Term): Theorem = {
    require(t1.typ == Bool, "Types of t1 and y2 must be Bool")
    val r1 = Variable(newVariable(t1.freeVariables, "r"), Bool)
    val old_def = \(r,r ==> bot)
    val new_def = \(r1,r1 ==> bot)
    val thm_not_renamed = TRANS(not_def, ALPHA_EQUIVALENCE(old_def, new_def)) // /\ == new_def
    val thm1 = AP_ARG(thm_not_renamed, t1) // /\(t1) == new_def(t1)
    val thm2 = TRANS(thm1, BETA_CONV(new_def(t1)))
    thm2
  }

  val TRUTH = EQ_MP(SYM(top_def), REFL(\(x, x)))

  def TRUTH_ELIM(thm: Theorem): Theorem = {
    thm.f match{
      case App(App(Constant("=", eqt), l), `top`) => EQ_MP(SYM(thm), TRUTH)
      case App(App(Constant("=", eqt), `top`), r) => EQ_MP(thm, TRUTH)
      case _ => throw new IllegalArgumentException("thm mut be an equality between a term and T")
    }
  }

  def TRUTH_INTRO(thm: Theorem): Theorem = DEDUCT_ANTISYM_RULE(thm, TRUTH)

  def CONJ(thm1: Theorem, thm2: Theorem): Theorem ={
    val a1 = TRUTH_INTRO(thm1)
    val a2 = TRUTH_INTRO(thm2)
    val f = Variable(newVariable(occuringVarThm(thm1)++occuringVarThm(thm2), "$f"), BooleanOp)
    val b1 = AP_FUNC(f, a1)
    val inter = ABS(MK_COMB(b1, a2), f)
    EQ_MP(SYM(AND_THM(thm1.f, thm2.f)), inter)
  }

  def CONJ_PICK_1(thm:Theorem):Theorem = thm.f match {
    case App(App(/\, l), r) => {
      val thm1 = EQ_MP(AND_THM(l, r), thm)
      val x = Variable(newVariable(freeVarThm(thm), "$x"), Bool)
      val y = Variable(newVariable(freeVarThm(thm), "$y"), Bool)
      val f = Variable(newVariable(freeVarThm(thm), "$f"), BooleanOp)
      val thm2 = AP_ARG(thm1, \(x, \(y, x)) )  //  \f. f l r/ (\xy. x) == \f. f T T/ (\xy. x)
      val thm3 = TRANS(SYM(BETA_CONV( \(f, f(l)(r))(\(x, \(y, x))) )  ), thm2)   //    \x.\y. x// l r  ==  \f. f l r/ (\xy. x) == \f. f T T/ (\xy. x)
      val thm4 = TRANS(SYM(AP_ARG(BETA_CONV( \(x, \(y, x))(l)), r )  ), thm3)  //  \y. l/ r == \x \y. x// l r == \f. f T T/ (\xy. x)
      val thm5 = TRANS(SYM(BETA_CONV( \(y, l)(r) )  ), thm4)  //  l == \y. l/ r == \f. f T T/ (\xy. x)
      val thm6 = TRANS(thm5, BETA_CONV( \(f, f(top)(top))(\(x, \(y, x)))  ))   //    l== \f. f T T/ (\xy. x) == \x.\y. x// T T
      val thm7 = TRANS(thm6, AP_ARG(BETA_CONV( \(x, \(y, x))(top) ), top))  //  l == \x.\y. x// T T == \y. T/
      print(thm7)
      val thm8 = TRANS(thm7, BETA_CONV( \(y, top)(top)  ))  //  l == \y. T/ == T
      thm8
    }
  }
  def CONJ_PICK_2(thm:Theorem):Theorem = thm.f match {
    case App(App(/\, l), r) => {
      val thm1 = EQ_MP(AND_THM(l, r), thm)
      val x = Variable(newVariable(freeVarThm(thm), "$x"), Bool)
      val y = Variable(newVariable(freeVarThm(thm), "$y"), Bool)
      val f = Variable(newVariable(freeVarThm(thm), "$f"), BooleanOp)
      val thm2 = AP_ARG(thm1, \(x, \(y, y)) )  //  \f. f l r/ (\xy. x) == \f. f T T/ (\xy. x)
      val thm3 = TRANS(SYM(BETA_CONV( \(f, f(l)(r))(\(x, \(y, y))) )  ), thm2)   //    \x.\y. x// l r  ==  \f. f l r/ (\xy. x) == \f. f T T/ (\xy. x)
      val thm4 = TRANS(SYM(AP_ARG(BETA_CONV( \(x, \(y, y))(l)), r )  ), thm3)  //  \y. l/ r == \x \y. x// l r == \f. f T T/ (\xy. x)
      val thm5 = TRANS(SYM(BETA_CONV( \(y, y)(r) )  ), thm4)  //  l == \y. l/ r == \f. f T T/ (\xy. x)
      val thm6 = TRANS(thm5, BETA_CONV( \(f, f(top)(top))(\(x, \(y, y)))  ))   //    l== \f. f T T/ (\xy. x) == \x.\y. x// T T
      val thm7 = TRANS(thm6, AP_ARG(BETA_CONV( \(x, \(y, y))(top) ), top))  //  l == \x.\y. x// T T == \y. T/
      print(thm7)
      val thm8 = TRANS(thm7, BETA_CONV( \(y, y)(top)  ))  //  l == \y. T/ == T
      thm8
    }
  }

}
