package semper.sil.ast

import utility.ControlFlowGraph
import utility.AstGenerator

/** A common trait for basic blocks. */
sealed trait Block {
  def succs: Seq[Edge]
  final override def equals(o: Any) = o match {
    case o: AnyRef => this eq o
    case _ => false
  }
  final override def hashCode = System.identityHashCode(this)

  /**
   * Returns a DOT representation of the control flow graph that can be visualized using
   * tools such as Graphviz.
   */
  def toDot = ControlFlowGraph.toDot(this)

  /**
   * Returns an AST representation of this control flow graph.
   */
  def toAst = AstGenerator.toAst(this)

  /**
   * See [[ControlFlowGraph.writtenVars]]
   */
  def writtenVars = ControlFlowGraph.writtenVars(this)
}

object Block {
  private var id: Int = 0
}

/**
 * A statement block is a block whose body contains a statement, which is the most common type
 * of blocks.
 */
sealed trait StatementBlock extends Block {
  def stmt: Stmt
}

object StatementBlock {
  def unapply(sb: StatementBlock) = Some((sb.stmt, sb.succs))
}

/** A control flow edge. */
sealed trait Edge {
  def dest: Block
}

/** A conditional control flow edge. */
case class ConditionalEdge(dest: Block, cond: Exp) extends Edge

/** An unconditional control flow edge. */
case class UnconditionalEdge(dest: Block) extends Edge

/** A basic block without outgoing edges. */
case class TerminalBlock(stmt: Stmt) extends StatementBlock {
  lazy val succs = Nil
}

/** A basic block with one outgoing edges. */
case class NormalBlock(stmt: Stmt, var succ: Block) extends StatementBlock {
  lazy val succs = List(UnconditionalEdge(succ))
}

/** A basic block with two outgoing edges that are conditional. */
case class ConditionalBlock(stmt: Stmt, cond: Exp, var thn: Block, var els: Block) extends StatementBlock {
  lazy val succs = List(ConditionalEdge(thn, cond), ConditionalEdge(els, Not(cond)(NoPosition)))
}

/** A loop block with an implicit conditional back edge, and one unconditional outgoing edge. */
case class LoopBlock(var body: Block, cond: Exp, invs: Seq[Exp], locals: Seq[LocalVarDecl], var succ: Block)
                    (val pos: Position = NoPosition, val info: Info = NoInfo)
      extends Block {

  lazy val succs = List(UnconditionalEdge(succ))
}

/** Corresponds to the `FreshReadPerm` statement, that is, the `vars` can be constrained inside the `body`. */
case class FreshReadPermBlock(vars: Seq[LocalVar], var body: Block, var succ: Block) extends Block {
  lazy val succs = List(UnconditionalEdge(succ))
}
