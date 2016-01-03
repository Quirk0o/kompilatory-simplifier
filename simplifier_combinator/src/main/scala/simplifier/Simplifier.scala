package simplifier

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  def simplify(node: Node): Node = node match {
    case NodeList(list) => NodeList(list.map(simplify))
    case e @ BinExpr(_, _, _) => simplifyBinExpr(e)
    case _ => node
  }

  def simplifyBinExpr(binExpr: Node): Node = binExpr match {
    case BinExpr("+", t1 @ Tuple(_), t2 @ Tuple(_)) => concatTuples(t1, t2)
    case BinExpr(op, left, right) =>
      val e = BinExpr(op, simplify(left), simplify(right))
      if (e.left != left || e.right != right)
        simplifyBinExpr(e)
      else
        e
  }

  def concatTuples(t1: Tuple, t2: Tuple) = Tuple(t1.list ++ t2.list)

}
