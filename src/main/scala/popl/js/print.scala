package popl.js

import org.bitbucket.inkytonik.kiama.output.PrettyPrinter
import ast._
import Bop._, Uop._, Typ._, Mut._

object print extends PrettyPrinter:
  override val defaultIndent = 2

  /*
   * Pretty-print values.
   *
   * We do not override the toString method so that the abstract syntax can be printed
   * as is.
   */
  def prettyVal(v: Expr): String =
    require(isValue(v))
    (v: @unchecked) match
      case Num(n) => n.toString
      case Bool(b) => b.toString
      case Str(s) => s
      case Undefined => "undefined"
      case Addr(a) => s"@$a"
      case Function(p, _, _, _) =>
        "[Function%s]".format(p match { case None => "" case Some(s) => ": " + s })

  def prettyVal(m: Mem, v: Expr): String =
    (v: @unchecked) match
      case a @ Addr(_) if m.contains(a) =>
        m(a) match
          case v: Val => prettyVal(m, v)
          case Obj(fs) =>
            val pretty_fields =
            fs map {
              case (f, Str(s)) => f + ": '" + s + "'"
              case (f, v) => f + ": " + prettyVal(m, v)
            } reduceRight {
              (s, acc) => s + ",\n  " + acc
            }
            "{ %s }".format(pretty_fields)
      case _ => prettyVal(v)


  /*
   * Determine precedence level of top-level constructor in an expression
   */
  def prec(e: Expr): Int =
    e match
      case v: Val => 0
      case Var(_) => 0
      case ObjLit(_) => 0
      case Print(_) | Call(_, _) => 1
      case UnOp(_, _) => 2
      case BinOp(bop, _, _) =>
        bop match
          case Times | Div => 3
          case Plus | Minus => 4
          case Gt | Ge | Lt | Le => 6
          case Eq | Ne => 7
          case And => 11
          case Or => 12
          case Assign => 16
          case Seq => 17        
      case If(_, _, _) | Decl(_, _, _, _) => 15
    

  def showTyp(typ: Typ): Doc = 
    typ match
      case TBool => "Bool"
      case TNumber => "Num"
      case TString => "String"
      case TUndefined => "Undefined"
      case TFunction(targ, tret) =>
        parens(showTyp(targ)) <+> "=>" <+> showTyp(tret)
      case TObj(tfs) =>
        val break = tfs.size > 3
        val sep = if break then comma <> line else comma <> softline
        if break 
        then braces(nest(line <> indent(showFieldList(tfs.toList, sep)) <> line))
        else braces(nest(emptyDoc <+> showFieldList(tfs.toList, sep) <+> emptyDoc))


  def showFieldList(txs: List[(String, (Mut, Typ))], sep: Doc): Doc =
    ssep(txs map { case (x, (m, t)) => showTId((x, (Some(m), t))) }, sep)

  def showTIdList(tx: Param, sep: Doc = comma <> space): Doc =
    showTId((tx._1, (None, tx._2)))

  def showMut(m: Mut): Doc = m match
    case MConst => "const"
    case MLet => "let"
      
  def showTId(tid: (String, (Option[Mut], Typ))): Doc =
    tid match
      case (x, (None, t)) =>
        x <> colon <+> showTyp(t)
      case (x, (Some(m), t)) =>
        showMut(m) <+> x <> colon <+> showTyp(t)

  /* Associativity of binary operators */
  enum Assoc:
    case Left, Right
  import Assoc._

  /*
   * Get associativity of a binary operator
   * (all current operators are left-associative)
   */
  def assoc(bop: Bop): Assoc = bop match
    case _ => Left

  /*
   * Pretty-print expressions in concrete JavaScript syntax.
   */
  def showJS(e: Expr): Doc =
    def showDecl(m: Mut, x: String, e1: Expr): Doc =
      val mut = m match
        case MConst => "const"
        case MLet => "let"
      mut <+> x <+> "=" <+>
        nest(showJS(e1)) <> semi <> line

    e match
      case Undefined => "undefined"
      case Num(d) => value(d)
      case Bool(b) => b.toString()
      case Str(s) => "'" <> s <> "'"
      case Addr(a) => s"@$a"
      case Var(x) => x
      case eu@UnOp(uop, e) =>
        val op: Doc => Doc = uop match
          case UMinus => "-" <+> _
          case Not => "!" <+> _
          case Deref => "*" <+> _
          case FldDeref(f) => _ <> "." <> f
        op(if prec(e) < prec(eu) then showJS(e) else parens(showJS(e)))
      case BinOp(bop, e1, e2) =>
        val op: Doc = bop match
          case Plus => " + "
          case Minus => " - "
          case Times => " * "
          case Div => " / "
          case And => " && "
          case Or => " || "
          case Eq => " === "
          case Ne => " !== "
          case Lt => " < "
          case Le => " <= "
          case Gt => " > "
          case Ge => " >= "
          case Assign => " = "
          case Seq =>
            if isStmt(e2) then ";" <> line else ", "

        def eToDoc(e1: Expr, as: Assoc): Doc =
          if prec(e1) < prec(e) || prec(e1) == prec(e) && as == assoc(bop) 
          then showJS(e1)
          else parens(showJS(e1))

        eToDoc(e1, Left) <> op <> eToDoc(e2, Right)

      case ei@If(e1, e2, e3) =>
        def eToDoc(e: Expr): Doc =
          if prec(e) < prec(ei)
          then showJS(e)
          else parens(showJS(e))
        eToDoc(e1) <+> "?" <+> eToDoc(e2) <+> ":" <+> eToDoc(e3)

      case Print(e) =>
        "console.log" <> parens(showJS(e))
      case Decl(m, x, e1, e2) =>
        showDecl(m, x, e1) <> line <> showJS(e2)
      case Call(e0, e1@BinOp(Seq, _, _)) if isStmt(e1) =>
        showJS(e0) <> parens(braces(line <> indent(showJS(e1)) <> line))
      case Call(e0, e1) =>
        showJS(e0) <> parens(showJS(e1))
      case Function(p, xs, tann, e) =>
        def showReturn(e: Expr): Doc = e match
          case BinOp(Seq, e1, e2) =>
            line <> showJS(e1) <> semi <> showReturn(e2)
          case Decl(m, x, e1, e2) =>
            line <> showDecl(m, x, e1) <> showReturn(e2)
          case Undefined => emptyDoc
          case e => line <> "return" <+> showJS(e)

        val name = p getOrElse ""
        val params = parens(showTIdList(xs))
        val rtyp = tann map (":" <+> showTyp(_)) getOrElse emptyDoc
        "function" <+> name <> 
          params <> rtyp <+> braces(nest(showReturn(e)) <> line)
      case ObjLit(fs) =>
        val hasFun = fs exists { case (_, (_, e)) => hasFunction(e) }
        val sep =
          if hasFun then comma <> line
          else comma <+> softline
        val fields = fs map {
          case (f, (mut, e)) => showMut(mut) <+> f <> colon <+> nest(showJS(e))
        } reduceOption {
          (f1, f2) => f1 <> sep <> f2
        } getOrElse emptyDoc
        if hasFun then braces(nest(nest(line <> fields) <> line))
        else braces(emptyDoc <+> nest(fields) <+> emptyDoc)  
  end showJS

  def prettyAST(x: Any): String = pretty(any(x)).layout

  def prettyJS(e: Expr): String = pretty(showJS(e)).layout

  def prettyTyp(typ: Typ): String = pretty(showTyp(typ)).layout

