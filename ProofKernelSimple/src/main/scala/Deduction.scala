import Core._
import Sugar._
import Theorems._
import PrettyPrinter._
import Helper._
import stainless.collection.List

object Deduction {

  //  |- \x. t (n) = t[n/x]
  def _BETA_CONV(t:Term) : Theorem = {
    t match {
      case App(\(x, t), n) => {
        require(n.freeVariables.forall(!t.bindingVariables.contains(_))) // BETA(x, t) = \x t/(x) == t
        _INST(BETA(x, t), x, n)  // INST(\x t/(x) == t, x, n)  =        \x t/(n) == t[n/x]   iff n has no free variables bound in t, and dos not contain x.
      }                                     // EQ_MP                                t[n/x] iff n has no free variables bound int, and dos not contain x.
      case _ => throw new IllegalArgumentException("BETA_CONV: The theorem must be of the form App(\\(x, t), n)")
    }
  }
  //  |- x = y
  //  |- f(x) = f(y)
  def AP_FUNC(f: Term, thm: Theorem): Theorem = {
    thm.f match {
      case App(App(Constant("=", _), x), y)  => {
        if (f.typ.in == x.typ)
          MK_COMB(REFL(f), thm)
        else
          throw new IllegalArgumentException("AP_ARG: input type of f and type of equality member don't match")
      }
      case _ => throw new IllegalArgumentException("AP_ARG: The theorem must be of the form x = y")
    }
  }
  //  |- f = g
  //  |- f(x) = g(x)
  def AP_ARG(thm: Theorem, x: Term): Theorem = {
    thm.f match {
      case App(App(Constant("=", _), f), g)  => {
        if (f.typ.in == x.typ)
          MK_COMB(thm, REFL(x))
        else
          throw new IllegalArgumentException("AP_FUNC: input type of euality members and type of x don't match")
      }
      case _ => throw new IllegalArgumentException("AP_ARG: The theorem must be of the form f = g")
    }
  }

  //  |- x=y
  //  |- y=x
  def SYM(thm: Theorem): Theorem ={
    thm.f match {
      case App(App(Constant("=", t), x), y)  => {
        _EQ_MP(AP_ARG(AP_FUNC(Constant("=", t), thm), x), REFL(x))
      }
      case _ => throw new IllegalArgumentException("AP_ARG: The theorem must be of the form f = g")
    }
  }

  def _AGNOSTIC_TRANS(first: Theorem, second: Theorem):Theorem = {
    (first.f, second.f) match {
      case (Application(Application(Constant("=", _), s), t), Application(Application(Constant("=", _), u), v)) =>
        if (t == u) _TRANS(first, second)
        else if (t == v) _TRANS(first, SYM(second))
        else if (s == u) _TRANS(SYM(first), second)
        else if (s == v) _TRANS(SYM(first), SYM(second))
        else throw new IllegalArgumentException("AGNOSTIC_TRANS: No two parts of equalities are equal")
      case _ => throw new IllegalArgumentException("AGNOSTIC_TRANS: Not two equalities")
    }
  }
  // |-
  // |- \x. t = \y t[y/x] if y is not free in t
  def _ALPHA_CONV(t: Term, x: Variable, y: Variable): Theorem ={  // Need that y never appears in t !
    //println("_ALPHA_CONV: Variables = "+prettyPrint(x, false)+", "+prettyPrint(y, false)+". Term = ")
    //print(t)
    require(!t.occuringVariables.contains(y)) // t.bindingVariables.contains(y) is bad for INST, t.freeVariables.contains(y) bad for ETA}
    if (x == y) REFL(\(x, t))
    val int0 = BETA(x, t)      //                              |-     \x. \x. x//(x) = \x. x/

    val int1 = ABS(_INST(int0, x, y), y)//                      |- \y. \x. \x. x//(x)/ = \y \x. x/[y/x]/
    val int2 = ETA(y, \(x, t))  //                                 \x. t = \y. \x. t/(y)/
    _AGNOSTIC_TRANS(int2, int1) //                                                \x. t = \y t[y/x]
  }

  //In every abstraction in t with bound variable x1, replace it by y1
  def _ALPHA_CONV_REC(t: Term, x1: Variable, y1: Variable): Theorem = {
    require(!t.occuringVariables.contains(y1), "ALPHA_CONV_REC: y1 is a free or binding variable in t")
    //println("_ALPHA_CONV_REC: Variables = "+prettyPrint(x1, false)+", "+prettyPrint(y1, false)+". Term = ")
    //print(t)
    t match {
      case Variable(name, variable_type) => REFL(t)
      case Abstraction(x, tInner) =>    //suppose tInner contains n
        if (x1 == x) {
          val fp = _ALPHA_CONV(tInner, x1, y1) // \x. tInner == \y. tInner[y/x]
          val acr = _ALPHA_CONV_REC(tInner, x1, y1) // tInner == tInner_ACR
          val fq = ABS(_INST(acr, x1, y1), y1) //                 \y. tInner[y/x] == \y. tInner_ACR[y/x]
          _TRANS(fp, fq)  // \x. tInner == \y. tInner_ACR
        }
        else ABS(_ALPHA_CONV_REC(tInner, x1, y1), x)
      case Application(f, arg) => MK_COMB(_ALPHA_CONV_REC(f, x1, y1), _ALPHA_CONV_REC(arg, x1, y1))
      case Constant(name, constant_type) => REFL(t)
    }
  }

  def ALPHA_EQUIVALENCE(t1: Term, t2: Term): Theorem ={
    require(areAlphaEquivalent(t1, t2), "t1 and t2 are not alpha equivalent") //In particuler, this lets us assume they have the exact same structure
    (t1, t2) match {
      case (Variable(n1, v1), Variable(n2, v2)) =>REFL(t1)
      case (\(a, s), \(b, t)) =>
        val z =  Variable(newVariable((t1.occuringVariables ++ t2.occuringVariables :+ a :+ b).unique, "$z"), a.typ)
        val thm1 = _ALPHA_CONV_REC(t1, a, z) // \a. s/ == \z. s[z/a],
        val thm2 = _ALPHA_CONV_REC(t2, b, z) // \b. t/ == \z. t[z/b]
        val thm3 = ABS(ALPHA_EQUIVALENCE(swap(s, a, z), swap(t, b, z)), z) // \z. s[z/a]/ == \z. t[z/b]/
        //print(thm1);print(thm2);print(thm3)
        val thm4 = _TRANS(thm1, thm3) // \a. s/ == \z. t[z/b]/
        _TRANS(thm4, SYM(thm2))
      case (App(f1, arg1), App(f2, arg2)) => MK_COMB(ALPHA_EQUIVALENCE(f1, f2), ALPHA_EQUIVALENCE(arg1, arg2))
      case (Constant(n1, v1), Constant(n2, v2)) =>REFL(t1)
    }
  }

  //More powerfull versions of the basic deduction rules, where only alpha-equivalence is required instead of equality

  def TRANS(first: Theorem, second: Theorem): Theorem = {
    require(
      ((first.f, second.f) match {
        case (Application(Application(Constant("=", _), s), t), Application(Application(Constant("=", _), u), v)) => areAlphaEquivalent(t, u)
        case _ => false
      }) && areCompatible(first.env, second.env))
    (first.f, second.f) match { //safe_equal precondition
      case (Application(Application(Constant("=", ct1), s), t), Application(Application(Constant("=", ct2), u), v)) =>
        val eq_t_u = ALPHA_EQUIVALENCE(t, u)
        val eq_s_u = _TRANS(first, eq_t_u)
        val eq_s_v = _TRANS(eq_s_u, second)
        eq_s_v
    }
  }

  def EQ_MP(eq:Theorem, p: Theorem): Theorem ={
    require(
      (eq.f match {
        case Application(Application(Constant("=", _), l), r) => areAlphaEquivalent(l, p.f)
        case _ => false
      }) && areCompatible(eq.env, p.env)
    )
    eq.f match {
      case Application(Application(Constant("=", _), l), r) =>
        val eq2 = _TRANS(ALPHA_EQUIVALENCE(p.f, l), eq)
        _EQ_MP(eq2, p)
    }
  }


  def BETA_CONV(t1:Term) : Theorem = {
    t1 match {
      case App(\(x, t), n) => { // BETA(x, t) = \x t/(x) == t
        val binding = t.bindingVariables
        val fre = n.freeVariables
        val problematicBinders = binding.filter(fre.contains(_))
        if (problematicBinders.isEmpty){
          require(n.freeVariables.forall(!t.bindingVariables.contains(_)))
          _INST(BETA(x, t), x, n)  // INST(\x t/(x) == t, x, n)  =   \x. t/(n) == t[n/x]   iff n has no free variables bound in t, and dos not contain x.
        }
        else{
          println("bonjour")
          val tPrime = removeProblematicVariables(n.freeVariables, problematicBinders, t)
          val thmTTPrime = AP_ARG(ABS(ALPHA_EQUIVALENCE(t, tPrime), x), n)  //  \x.t/(n) == \x.tPrime/(n)
          _TRANS(thmTTPrime, _INST(BETA(x, tPrime), x, n)) // \x.t/(n) == \x. tPrime/(n) == tPrime[n/x]
          }
        }
      case _ => throw new IllegalArgumentException("BETA_CONV: The theorem must be of the form App(\\(x, t), n)")
    }
  }

}
