import Core._
import Theorems._
import Sugar._
import stainless.lang._

object PrettyPrinter {

  def prettyPrint(k:HOL_type):String = {
    k match {
      case Bool => "bool"
      case Ind => "*"
      case Unit => "Unit"
      case Func(a, r) => "["+prettyPrint(a)+"=>"+prettyPrint(r)+"]"
      case TypeVariable(name) => name
      case CustomType(name) => name
    }
  }

  def prettyPrint(t:Term, full:Boolean): String= {
    t match {
      case Application(Application(Constant("=", _, _), l), r) => "("+prettyPrint(l, full)+ " = " +prettyPrint(r, full)+")"
      case Variable(name, k) => if (full) name+":"+prettyPrint(k) else name
      case Abstraction(x, t) => "\\"+prettyPrint(x ,full) + ". " + prettyPrint(t, full)+"/"
      case Application(f, t) => prettyPrint(f, full) +"("+prettyPrint(t, full)+")"
      case Constant(name, constant_type, _) => name
    }
  }
  def prettyPrint(thm: Theorem, full:Boolean): String ={
    "{"+ thm.c.map(f => prettyPrint(f, full)).toScala.mkString(", ")+ "} |- " + prettyPrint(thm.f, full)
  }


  def print(k: HOL_type): Unit = println(prettyPrint(k))
  def print(t:Term): Unit = println(prettyPrint(t, false))
  def print(thm:Theorem): Unit = println(prettyPrint(thm, false))

}
