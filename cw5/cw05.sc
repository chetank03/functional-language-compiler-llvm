// CW 2
//======



// Rexp
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp
case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class FROM(r: Rexp, n: Int) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp  

// Values, you might have to extend them 
// according to which values you want to create
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
case class Range(s: Set[Char]) extends Val
case class Plus(vs: List[Val]) extends Val
case class Optional(v: Val) extends Val
case class Ntimes(vs: List[Val]) extends Val



// Convenience for typing
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}

implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)


extension (s: String) {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def & (r: Rexp) = RECD(s, r)
}

extension (r: Rexp) {
  def ~ (s: Rexp) = SEQ(r, s)
  def % = STAR(r)
  def | (s: Rexp) = ALT(r, s)
}


//nullable
def nullable(r: Rexp): Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  //Extended Regular Expressions for nullable
  case RANGE(_) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(_) => true
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
  case RECD(_, r1) => nullable(r1)
  
}


// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp): Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))

  //Extended Regular Expressions for derivatives
  case RANGE(cs) => if (cs.contains(c)) ONE else ZERO
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case OPTIONAL(r) => der(c,r)
  case FROM(r, n) =>
    if (n == 0) SEQ(der(c, r), STAR(r)) else SEQ(der(c, r), FROM(r, n - 1))
  case NTIMES(r1, n) =>
    if (n == 0) ZERO
    else SEQ(der(c, r1), NTIMES(r1, n - 1))
  case RECD(_, r1) => der(c, r1)
}

// Flatten
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Range(s) => s.toString
  case Plus(vs) => vs.map(flatten).mkString
  case Optional(v) => flatten(v)
  case Ntimes(vs) => vs.flatMap(flatten).mkString
  case Rec(x, v) => flatten(v)
}

// Env
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Range(v) => Nil
  case Rec(x, v) => (x, flatten(v))::env(v)
  case Plus(vs) => vs.flatMap(env)
  case Optional(v) => env(v)
  case Ntimes(vs) => vs.flatMap(env)
}

// Mkeps
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  // Extended mkeps clauses
  case RECD(x, r) => Rec(x, mkeps(r))
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => Stars(Nil)
  case NTIMES(r, n) => Stars(List.fill(n)(mkeps(r)))
}


// Inj
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  // Extended Inj clauses
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (RANGE(_), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), v) => Stars(inj(r, c, v)::Nil)
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
}


// Rectification functions
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// Simp
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// Lex
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def ders_simp(cs: List[Char], r: Rexp) : Rexp = cs match {
  case Nil => r
  case c::cs => ders_simp(cs, simp(der(c, r))._1)
} 

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))

// Language specific code

val KEYWORD : Rexp = "if" | "then" | "else" | "true" | "false" | "skip" | "val" | "print_int" | "print_char"| "print_string"| "print_star" | "new_line" | "def" 
val TYPE : Rexp = "Int" | "Double" | "String" | "Boolean" | "Void"
val OP : Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | "&&" | "||" | "="
val LET = RANGE(("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz").toSet)
val SYM : Rexp = RANGE(("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz.'\"-_><=;,:\\").toSet)
val PARENS : Rexp = "(" | ")" |"{" | "}"  
val COMMA : Rexp = ","
val SEMI : Rexp = ";"
val COLON : Rexp = ":"
val WHITESPACE : Rexp = PLUS(" ") | "\n" | "\t" | "\r"
val DIGIT : Rexp = RANGE(("0123456789").toSet)
val EOL: Rexp = "\n" | "\r\n"
val COMMENT : Rexp = "//" ~ (LET | DIGIT | SYM | PARENS | " ").% ~ EOL
val UPPERCASE_LET = RANGE(("ABCDEFGHIJKLMNOPQRSTUVWXYZ").toSet)
val LOWERCASE_LET = RANGE(("abcdefghijklmnopqrstuvwxyz").toSet)
val GLOBAL_CONST : Rexp = UPPERCASE_LET ~ ("_" | LET | DIGIT).%
val ID : Rexp = LOWERCASE_LET ~ ("_" | LET | DIGIT).%
val STRING : Rexp = "\"" ~ (SYM | DIGIT | PARENS | WHITESPACE).% ~ "\""
val NUM : Rexp = OPTIONAL("-") ~ ("0" | RANGE(("123456789").toSet) ~ DIGIT.%)
val DOUBLE : Rexp = NUM ~ "." ~ PLUS(DIGIT)
val CHAR_CONST : Rexp = "'" ~ (LET | DIGIT | SYM | PARENS | "\\n" | WHITESPACE) ~ "'"
val new_line : Rexp = "\\n"

val FUN_REGS = (("k" & KEYWORD) | 
                  ("t" & TYPE) | 
                  ("c" & COMMENT) |
                  ("char" & CHAR_CONST) |
                  ("str" & STRING) |
                  ("n" & NUM) |
                  ("d" & DOUBLE) |
                  ("o" & OP) | 
                  ("p" & PARENS) |
                  ("comma" & COMMA) |
                  ("colon" & COLON) |
                  ("s" & SEMI) | 
                  ("g" & GLOBAL_CONST) |
                  ("i" & ID) |
                  ("w" & WHITESPACE) | 
                  ("e" & EOL)).%  

def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

// Token
abstract class Token extends Serializable 
case class T_KEYWORD(s: String) extends Token
case class T_TYPE(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STRING(s: List[Int]) extends Token
case object T_COLON extends Token
case class T_PAREN(s: String) extends Token
case object T_COMMA extends Token
case object T_SEMI extends Token
case class T_COMMENT(s: String) extends Token
case class T_SYM(s: String) extends Token
case class T_ID(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_DOUBLE(n: Double) extends Token
case class T_EOL(s: String) extends Token
case class T_GLOBAL_CONST(s: String) extends Token
case class T_CHAR(c: Int) extends Token

val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KEYWORD(s)
  case ("t", s) => T_TYPE(s)
  case ("o", s) => T_OP(s)
  case ("str", s) => T_STRING(s.drop(1).dropRight(1).map(_.toInt).toList)
  case ("char", s) if (s(1) == 92 && s(2) == 110) => T_CHAR(10)
  case ("char", s) => T_CHAR(s(1).toInt)
  case ("p", s) => T_PAREN(s)
  case ("comma", _) => T_COMMA
  case ("colon", s) => T_COLON
  case ("s", _) => T_SEMI
  case ("g", s) => T_GLOBAL_CONST(s)
  case ("i", s) => T_ID(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("d", s) => T_DOUBLE(s.toDouble)
}

// Tokenise
def tokenise(s: String) : List[Token] = {
  val tks = lexing_simp(FUN_REGS, s).collect(token)
  if (tks.length != 0) tks
  else { println (s"Tokenise Error") ; sys.exit(-1) }     
}


// println(tokenise(os.read(os.pwd / "fact.fun")))
// Parser

import scala.language.implicitConversions    
import scala.language.reflectiveCalls


type IsSeq[I] = I => Seq[_]

abstract class Parser[I, T](using is: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(p => is(p._2).isEmpty) match {
      case (good, _) if !good.isEmpty => good.head._1
      case (_, err) => { println (s"Parse Error\n${err.minBy(p => is(p._2).length)}") ; sys.exit(-1) }
    }
}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

// parser combinators

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}


case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) : Parser[List[Token], Token] = TokParser(t)

def ListParser[I, T, S](p: => Parser[I, T], q: => Parser[I, S])(using is: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)).map{ case (x:T) ~ (y:S) ~ (z:List[T]) => x :: z } ||
  (p.map[List[T]]{s => List(s)})
}

case object CharParser extends Parser[List[Token], Int] {
  def parse(tokens: List[Token]): Set[(Int, List[Token])] = tokens match {
      case T_CHAR(c) :: rest => Set((c, rest))
      case _ => Set.empty
    }
}

case object StringParser extends Parser[List[Token], List[Int]] {
  def parse(tokens: List[Token]): Set[(List[Int], List[Token])] = tokens match {
      case T_STRING(s) :: rest => Set((s, rest))
      case _ => Set.empty
    }
}

case object IdParser extends Parser[List[Token], String] {
  def parse(tokens: List[Token]): Set[(String, List[Token])] = tokens match {
      case T_ID(s) :: rest => Set((s, rest))
      case _ => Set.empty
    }
}

case object GlobalConstParser extends Parser[List[Token], String] {
  def parse(tokens: List[Token]): Set[(String, List[Token])] = tokens match {
      case T_GLOBAL_CONST(s) :: rest => Set((s, rest))
      case _ => Set.empty
    }
}

case object TypeParser extends Parser[List[Token], String] {
  def parse(tokens: List[Token]): Set[(String, List[Token])] = tokens match {
      case T_TYPE(s) :: rest => Set((s, rest))
      case _ => Set.empty
    }
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(tokens: List[Token]): Set[(Int, List[Token])] = tokens match {
      case T_NUM(n) :: rest => Set((n, rest))
      case _ => Set.empty
    }
}
 
case object DoubleParser extends Parser[List[Token], Double] {
  def parse(tokens: List[Token]): Set[(Double, List[Token])] = tokens match {
      case T_DOUBLE(n) :: rest => Set((n, rest))
      case _ => Set.empty
    }
}

case object EolParser extends Parser[List[Token], String] {
  def parse(tokens: List[Token]): Set[(String, List[Token])] =
    tokens match {
      case T_EOL(s) :: rest => Set((s, rest))
      case _ => Set.empty
    }
}

// some convenient syntax for parser combinators
extension [I: IsSeq, T](p: Parser[I, T]) {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String, args: List[(String, String)], ty: String, body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String, v: Int) extends Decl
case class FConst(name: String, x: Double) extends Decl

case class Call(name: String, args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp  // integer numbers
case class FNum(i: Double) extends Exp  // float numbers
case class StrConst(s: List[Int]) extends Exp  // string constants
case class ChConst(c: Int) extends Exp  // character constants
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp  // expressions separated by semicolons
case class Bop(o: String, a1: Exp, a2: Exp) extends BExp

// Grammar Rules for the Fun language

// arithmetic expressions
lazy val Exp: Parser[List[Token], Exp] = 
  (T_KEYWORD("if") ~ BExp ~ T_KEYWORD("then") ~ Exp ~ T_KEYWORD("else") ~ Exp).map{ case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
  (M ~ T_SEMI ~ Exp).map{ case x ~ _ ~ y => Sequence(x, y): Exp } || M
lazy val M: Parser[List[Token], Exp] =
  (T_KEYWORD("print_int") ~ L).map{ case _ ~ y => Call("print_int", List(y)): Exp } || 
  (T_KEYWORD("print_char") ~ L).map{ case _ ~ y => Call("print_char", List(y)): Exp } ||
  (T_KEYWORD("print_string") ~ L).map{ case _ ~ y => Call("print_string", List(y)): Exp } ||
  (T_KEYWORD("print_star") ~ T_PAREN("(") ~ T_PAREN(")")).map{ case _ ~ _ ~ _ => Call("print_star", List()): Exp } ||
  (T_KEYWORD("print_space") ~ L).map{ case _ ~ _ => Call("print_space", List()): Exp } ||
  (T_KEYWORD("skip") ~ T_PAREN("(") ~ T_PAREN(")")).map{ case _ ~ _ ~ _ => Call("skip", List()): Exp } ||
  (T_KEYWORD("skip")).map{ case _ => Call("skip", List()): Exp } ||
  (T_KEYWORD("new_line") ~ T_PAREN("(") ~ T_PAREN(")")).map{ case _ ~ _ ~ _ => Call("new_line", List()): Exp } || L
lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp).map{ case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp).map{ case x ~ _ ~ z => Aop("-", x, z): Exp } || T  
lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T).map{ case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T).map{ case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T).map{ case x ~ _ ~ z => Aop("%", x, z): Exp } || F
lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_PAREN("(") ~ T_PAREN(")")).map{ case x ~ _ ~ _ => Call(x, List()): Exp } ||
  (IdParser ~ T_PAREN("(") ~ ListParser(Exp, T_COMMA) ~ T_PAREN(")")).map{ case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
  (T_PAREN("(") ~ Exp ~ T_PAREN(")")).map{ case _ ~ y ~ _ => y: Exp } || 
  (T_PAREN("{") ~ Exp ~ T_PAREN("}")).map{ case _ ~ y ~ _ => y: Exp } ||
  IdParser.map{ case x => Var(x): Exp } || 
  CharParser.map{ case x => ChConst(x): Exp } ||
  StringParser.map{ case x => StrConst(x): Exp } ||
  GlobalConstParser.map{ case x => Var(x): Exp } ||
  NumParser.map{ case x => Num(x): Exp } ||
  DoubleParser.map{ case x => FNum(x): Exp }

// boolean expressions
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp).map{ case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp).map{ case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", x, z): BExp } ||  
  (Exp ~ T_OP("=>") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", z, x): BExp }  

lazy val Defn: Parser[List[Token], Decl] =
  (T_KEYWORD("val") ~ GlobalConstParser ~ T_COLON ~ T_TYPE("Int") ~ T_OP("=") ~ NumParser).map{ case _ ~ y ~ _ ~ r ~ _ ~ s => Const(y, s): Decl } ||
  (T_KEYWORD("val") ~ GlobalConstParser ~ T_COLON ~ T_TYPE("Double") ~ T_OP("=") ~ DoubleParser).map{ case _ ~ y ~ _ ~ r ~ _ ~ s => FConst(y, s): Decl } ||
  (T_KEYWORD("def") ~ IdParser ~ T_PAREN("(") ~ ListParser(IdParser ~ T_COLON ~ TypeParser, T_COMMA) ~ T_PAREN(")") ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp).map{ case _ ~ y ~ _ ~ w ~ _ ~ _ ~ t ~ _ ~ r => Def(y, w.map{case x ~ _ ~ z => (x,z)}, t, r): Decl } ||
  (T_KEYWORD("def") ~ IdParser ~ T_PAREN("(") ~ T_PAREN(")") ~ T_COLON ~ TypeParser ~ T_OP("=") ~ Exp).map{ case _ ~ y ~ _ ~ _ ~ _ ~ t ~ _ ~ r => Def(y,Nil,t,r): Decl }

lazy val Prog: Parser[List[Token], List[Decl]] =
  (Defn ~ T_SEMI ~ Prog).map{ case x ~ _ ~ z => x :: z : List[Decl] } ||
  (Exp.map((s) => List(Main(s)) : List[Decl]))

def parse_tks(tks: List[Token]) : List[Decl] = 
  Prog.parse_single(tks)


// Reading tokens and Writing parse trees
// pre-2.5.0 ammonite 
// import ammonite.ops._
// post 2.5.0 ammonite
// import os._
def parseCodeFromFile(fileName: String): Unit = {
  val code = os.read(os.pwd / fileName)
  val tokens = tokenise(code)
  val result2 = parse_tks(tokens)
  println(result2)
}

// For generating new labels.
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// typing
type Ty = String
type TyEnv = Map[String, Ty]

// initial typing environment
val initialEnv = Map[String, Ty]("skip" -> "Void", "print_int" -> "Void", "print_char" -> "Void",
                                "print_space" -> "Void", "print_star" -> "Void", "new_line" -> "Void")

val typeConversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")

// Internal CPS (intermediate) language for FUN.
abstract class KExp
abstract class KVal

case class KVar(s: String , ty: String = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(i: Double) extends KVal
case class KChConst(i: Int) extends KVal
case class KStrConst(s: List[Int]) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KGlobal(s: String) extends KVal
case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp

def typ_val(v: KVal, ts: TyEnv) : String = v match {
  case KVar(x, t) => ts(x)
  case KGlobal(x) => ts(x)
  case KNum(_) => "Int"
  case KFNum(_) => "Double"
  case KChConst(_) => "Int"
  case Kop("=", v1, v2) => typ_val(v2, ts)
  case Kop(_, v1, v2) => {
    val typ_v1 = typ_val(v1, ts)
    val typ_v2 = typ_val(v2, ts)
    if (typ_v1 == typ_v2) typ_v1 else "UNDEF"
  }
  case KCall(o, _) => ts.getOrElse(o, "UNDEF")
}

def typ_exp(a: KExp, ts: TyEnv) : String = a match {
  case KLet(x, e1, e2) => typ_exp(e2, ts + (x -> typ_val(e1, ts)))
  case KIf(x, e1, e2) => {
    val typ_e1 = typ_exp(e1, ts)
    val typ_e2 = typ_exp(e2, ts)
    if (typ_e1 == typ_e2) typ_e1 else "UNDEF"
  }
  case KReturn(v) => typ_val(v, ts)
}

// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) => {
    if(s.head.isUpper) {
      val f = Fresh("tmp")
      KLet(f, KGlobal(s), k(KVar(f)))
    } else {
      k(KVar(s))
    }
  }
  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case ChConst(i) => k(KChConst(i))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
}

def CPSi(e: Exp) = CPS(e)(KReturn)

// Convenient string interpolations 
// for instructions, labels and methods.
import scala.language.implicitConversions
import scala.language.reflectiveCalls
extension (sc: StringContext) {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

def compile_type(s: String) : String = typeConversion.getOrElse(s, s)

def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "%" => "srem i32"
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32 "
  case "<=" => "icmp sle i32 " // Signed less or equal.
  case "<" => "icmp slt i32 " // Signed less than.
}
def compile_dop(op: String) = op match {
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "%" => "frem double"
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "
  case "<" => "fcmp olt double "
}
// Compile K values.
def compile_val(v: KVal)(ts: TyEnv) : String = v match {
  case KNum(i) => s"$i"
  case KVar(s, _) => {
    if (ts.getOrElse(s, "UNDEF") == "Void") ""
    else s"%$s"
  }
  case KFNum(i) => s"$i"
  case KChConst(i) => s"$i"
  case KGlobal(s) => {
    val variable_type = compile_type(ts.getOrElse(s, "UNDEF"))
    s"load $variable_type, $variable_type* @$s"
  }
  case Kop(op, x1, x2) => 
    if(typ_val(v, ts) == "Int") s"${compile_op(op)} ${compile_val(x1)(ts)}, ${compile_val(x2)(ts)}"
    else s"${compile_dop(op)} ${compile_val(x1)(ts)}, ${compile_val(x2)(ts)}"
  case KCall(x1, args) => {
    val compiledArgs = args.map(arg => compile_type(typ_val(arg, ts)) ++ " " ++ compile_val(arg)(ts)).mkString(", ")
    s"call ${compile_type(ts.getOrElse(x1, "UNDEF"))} @$x1 ($compiledArgs)"
  }
}

// Compile K expressions.
def compile_exp(a: KExp)(ts: TyEnv) : String = a match {
  case KReturn(v) =>
    val returnType = compile_type(typ_exp(a, ts))
    if (returnType == "void") {
      "ret void"
    } else {
      i"ret $returnType ${compile_val(v)(ts)}"
    }
  case KLet(x: String, v: KVal, e: KExp) => v match {
    case KCall(x1, vrs) => {
      if (ts.getOrElse(x1, "UNDEF") == "Void") i"${compile_val(v)(ts)}" ++ compile_exp(e)(ts + (x -> "Void"))
      else i"%$x = ${compile_val(v)(ts)}" ++ compile_exp(e)(ts + (x -> typ_val(v, ts)))
    }
    case _ => i"%$x = ${compile_val(v)(ts)}" ++ compile_exp(e)(ts + (x -> typ_val(v, ts)))
  }
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1)(ts) ++
    l"\n$else_br" ++ 
    compile_exp(e2)(ts)
  }
}
// Compile function for declarations and main.
def compile_decl(d: Decl)(ts: TyEnv) : (String, TyEnv) = d match {
  case Def(name, args, ty, body) => {
    val updatedTypeEnv = args.foldLeft(ts + (name -> ty)) { case (acc, (argName, argType)) => acc + (argName -> argType) }
    val argsStr = args.map { case (argName, argType) => compile_type(argType) ++ " %" ++ argName }.mkString(", ")
    (m"define ${compile_type(ty)} @$name ($argsStr) {" ++
    compile_exp(CPSi(body))(updatedTypeEnv) ++
    m"}\n", updatedTypeEnv)
  }
  case Main(body) => {
    (m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0))))(ts) ++
    m"}\n", ts)
  }
  case Const(name, x) => {
    if(name.head.isUpper) (i"@$name = global i32 $x", ts + (name -> "Int"))
    else (i"%$name = i32 $x", ts + (name -> "Int"))
  }
  case FConst(name, x) => {
    if(name.head.isUpper) (i"@$name = global double $x", ts + (name -> "Double"))
    else (i"%$name = double $x", ts + (name -> "Double"))
  }
}

def compile(prog: List[Decl], ts: TyEnv) : String = prog match {
  case Nil => ""
  case h::tl => {
    val (compiled_decl, updatedEnv) = compile_decl(h)(ts)
    compiled_decl ++ compile(tl, updatedEnv)
  }
}

// prelude
val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_int = private constant [3 x i8] c"%d\00"
@.str_c = private constant [3 x i8] c"%c\00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_int, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
  ret void
}

define void @print_char(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_c, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x)
  ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILT-IN FUNCTIONS (prelude)
"""

def fun_compile(prog: List[Decl]) : String = 
  prelude ++ compile(prog, initialEnv)

// Handy function for generating .ll files.
@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    val code = fun_compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}