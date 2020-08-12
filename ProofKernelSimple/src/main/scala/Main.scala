import Core._
import Theorems._
import PrettyPrinter._
import BasicConstants._
import Deduction._
import Sugar._
import stainless.lang.Set
import stainless.collection._

object Main {

  def main(args: Array[String]): Unit = {

    val x = Variable("x", Bool)
    val x2 = Variable("x2", Bool)
    val x3 = Variable("x3", Bool)
    val y = Variable("y", Bool)
    val z = Variable("z", Bool)
    val m = Variable("m", Ind)
    val n = Variable("n", Ind)
    val u = Variable("u", Ind)
    val A = TypeVariable("A")
    val xA = Variable("x", A)
    val l = Variable("lq", Bool)
    val r = Variable("rq", Bool)
    val s = Variable("s", Bool)
    val ff = Variable("f", Func(Bool, Func(Bool, Bool)))
    val gg = Variable("g", Func(Bool, Func(Bool, Bool)))
    val PA = Variable("P", Func(A, Bool))


    val t1: Term = \-/(n, n === m)
    val t2: Term = \(y, \(gg, gg(\(y, y)(y) )(r) ))

    val thm1:Theorem = and_def
    val Single = CustomType("Single")
    val BotS = Constant("BtS", BooleanOp->Single, Nil())
    val StBo = Constant("StB", Single->BooleanOp, Nil())
    val bo = Variable("bo", BooleanOp)
    val t = \(bo, \-/(x, bo(x)(x) ))(<=>)
    print(GEN(REFL(x), x))
    val th1 = SYM( ASSUME(\(bo, \-/(x, bo(x)(x) ))(<=>) === \-/(x, <=>(x)(x))) )
    val th = EQ_MP(th1, GEN(REFL(x), x))
    print(th)
    val (thm2, thm3) = DEFINE_TYPE( Single, BooleanOp, th , BotS, StBo )
    print(thm2)
    print(thm3)




    /*
    val eps = Constant("e", Func( Func(A, Bool), A))
    val choice = Application(\-/, Abstraction(xA,
      Application(Application(==>,
        Application(PA, xA)), Application(PA, Application(eps, PA )
      ))
    ))

    val AX: Theorem = ASSUME(choice)

    println(prettyPrint(AX, false))



        val t = Abstraction(xA, Equal(top, Application(fA, xA)))

        val thm = ETA(yA, t)
        val thmI = INST(INST_TYPE(BETA(y, t), A, Ind), y, top)
        println(prettyPrint(thm, true))
        println(prettyPrint(thmI, true) )*/
  }
}
