import Core._
import Theorems._
import Deduction._
import BasicConstants._
import stainless.collection._
import Sugar._
import Helper._


object Arithmetic {
  private val x1 = Variable("x1", Ind)
  private val x2 = Variable("x2", Ind)
  private val x = Variable("x", Ind)
  private val y = Variable("y", Ind)


  val suc: Constant = Constant("Succ", Ind -> Ind, Nil())
  private val inf = \-/(x1, \-/(x2, (suc(x1) === suc(x2)) ==> (x1 === x2))) /\ ?(y, \-/(x, not(y === suc(x))))
  val INFINITY: Theorem = ASSUME(inf) //Assertion thst Ind is an infinite type: There exist an injective function Ind->Ind that is not surjective

  val N_0: Constant = Constant("0", Ind, Nil())
  val N_0_def : ConstantDefinition = ConstantDefinition( N_0, eps(\(y, \-/(x, not(y === suc(x))) )) )
}
