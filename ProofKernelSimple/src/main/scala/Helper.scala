import Core._
import Sugar._
import Theorems._
import PrettyPrinter._
import stainless.collection.List
import stainless.lang.decreases


object Helper {

  def newVariable(used: List[Variable], r: String) : String = { //Produces a variable name with enough ' so that there are no variable with this name in the list used
    decreases(used.size)
    val k = used.filter(_.name != r)
    if(k.size < used.size) newVariable(k, r+"'")
    else r
  }
  def fresh(t: Term, r: String): String = newVariable(t.freeVariables, r)
  def notOccuring(t: Term, r: String): String = newVariable(t.occuringVariables, r)

  def swap(t: Term, a: Variable, b: Variable): Term = {
    t match {
      case Variable(name, variable_type) => if (t == a) b else if (t == b) a else t
      case Abstraction(x, t) => Abstraction(if (x == a) b else if (x == b) a else x, swap(t, a, b))
      case Application(f, t) =>Application(swap(f, a, b), swap(t, a, b))
      case Constant(name, constant_type) => t
    }
  }

  def areAlphaEquivalent(t1:Term, t2:Term): Boolean = {
    (t1, t2) match {
      case (Variable(_, _), Variable(_, _)) => t1 == t2
      case (App(s1, s2), App(t1, t2)) => areAlphaEquivalent(s1, t1) && areAlphaEquivalent(s2, t2)
      case (\(a, s), \(b, t)) => a.typ == b.typ && {
        val z = Variable(newVariable((s.occuringVariables ++ t.occuringVariables :+ a :+ b).unique, "$z"), a.typ)
        areAlphaEquivalent(swap(s, a, z), swap(t, b, z))
      }
      case (Constant(_, _), Constant(_, _)) => t1 == t2
      case (_, _) => false
    }
  }

  def removeProblematicVariables(used: List[Variable], pb: List[Variable], te: Term): Term = { // t', Thm(te == t')
    if (pb.isEmpty) te
    else {
      val freshVar = newVariable((used ++ te.occuringVariables).unique, "$r")
      val tPrime = swap(te, pb.head, Variable(freshVar, pb.head.variable_type)) //
      removeProblematicVariables(used, pb.tail, tPrime)
    }
  }

  def freeVarThm(thm: Theorem): List[Variable] = (thm.f.freeVariables ++ thm.c.flatMap(_.freeVariables)).unique
  def occuringVarThm(thm: Theorem): List[Variable] = (thm.f.occuringVariables ++ thm.c.flatMap(_.occuringVariables)).unique

}
