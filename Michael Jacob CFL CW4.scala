// A Small Compiler for the WHILE Language
// (it does not use a parser nor lexer)

// A simple lexer inspired by work of Sulzmann & Lu
//==================================================


import java.io.Serializable

import scala.annotation.tailrec
import scala.collection.JavaConverters._
import scala.language.implicitConversions
import scala.language.reflectiveCalls
import scala.reflect.internal.Trees

// regular expressions including records
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp
case class STAR(r: Rexp) extends Rexp
case class RECD(x: String, r: Rexp) extends Rexp
case class CFUN(f: Char => Boolean) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp

val ALL = CFUN((c: Char) => true)
def CHAR(c: Char) = CFUN(_ == c)
def RANGE(cs: Set[Char]) = CFUN(cs.contains(_))

// values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp =
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CFUN(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case RECD(_, r1) => nullable(r1)
}

def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CFUN(f) => if (f(c)) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) =>
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case PLUS(r1) => SEQ(der(c,r1), STAR(r1))
  case OPTIONAL(r1) => der(c,r1)
  case NTIMES(r1, i) =>
    if (i == 0) ZERO else SEQ(der(c, r1), NTIMES(r1, i - 1))
  case RECD(_, r1) => der(c, r1)
}


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}


// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) =>
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => Stars(Nil)
  case NTIMES(r,i) => if (i == 0) Stars(Nil) else Stars(List.fill(i)(mkeps(r)))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CFUN(d), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), _) => Stars(List(inj(r, c, v)))
  case (NTIMES(r,i), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

def lex(r: Rexp, s: String) : Val = {
  if (s.isEmpty) (if (nullable(r)) mkeps(r) else throw new Exception("lexing error"))
  else inj(r,s.head,lex(der(s.head,r),s.tail))
}

// some "rectification" functions for simplification
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
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else
  { throw new Exception("lexing error") }
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) =
  env(lex_simp(r, s.toList))


// The Lexing Rules for the Fun Language

val chars = (' ' to '~').toList
val STRINGELIGIBLE : Rexp = RANGE(chars.filter(_ != '\"').toSet)
val LETTER : Rexp = RANGE("ABCDEFGHIJKLMNOPQRSTUVXYZabcdefghijklmnopqrstuvwxyz".toSet)
val SYM : Rexp = RANGE("ABCDEFGHIJKLMNOPQRSTUVXYZabcdefghijklmnopqrstuvwxyz_".toSet)
val DIGIT : Rexp = RANGE("0123456789".toSet)
val NONZERODIGIT : Rexp = RANGE("123456789".toSet)
val ID : Rexp = LETTER ~ (SYM | DIGIT).%
val NUM : Rexp = (NONZERODIGIT ~ DIGIT.%) | CHAR('0')
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "for" | "upto" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "%" | "/" | "||" | "&&"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val LPAREN: Rexp = "{" | "("
val RPAREN: Rexp = "}" | ")"
val STRING: Rexp = "\"" ~ (STRINGELIGIBLE | WHITESPACE).% ~ "\""


val WHILE_REGS = (("k" $ KEYWORD) |
  ("i" $ ID) |
  ("o" $ OP) |
  ("n" $ NUM) |
  ("s" $ SEMI) |
  ("str" $ STRING) |
  ("lp" $ LPAREN) |
  ("rp" $ RPAREN) |
  ("w" $ WHITESPACE)).%


// Two Simple While Tests
//========================

println("test: read n")

val prog0 = """read n"""
println(lexing_simp(WHILE_REGS, prog0))

println("test: read  n; write n ")

val prog1 = """read  n; write n"""
println(lexing_simp(WHILE_REGS, prog1))


// Bigger Tests
//==============

// escapes strings and prints them out as "", "\n" and so on
def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

val prog2 = """
write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "Result";
write minus2
"""

println("lexing Fib")
println(escape(lexing_simp(WHILE_REGS, prog2)).mkString("\n"))
println(escape(lexing_simp(WHILE_REGS, prog2)).filter(_._1 != "w").mkString("\n"))



val prog3 = """
start := 1000;
x := start;
y := start;
z := start;
while 0 < x do {
 while 0 < y do {
  while 0 < z do {
    z := z - 1
  };
  z := start;
  y := y - 1
 };
 y := start;
 x := x - 1
}
"""

println("lexing Loops")
println(escape(lexing_simp(WHILE_REGS, prog3)).mkString("\n"))
println(escape(lexing_simp(WHILE_REGS, prog3)).filter(_._1 != "w").mkString("\n"))

val prog4 = """
write "Input n please";
read n;
write "The factors of n are";
f := 2;
while n != 1 do {
  while (n / f) * f == n do {
    write f;
    n := n / f
  };
  f := f + 1
}
"""
println("factors")
println(escape(lexing_simp(WHILE_REGS, prog4)).mkString("\n"))
println(escape(lexing_simp(WHILE_REGS, prog4)).filter(_._1 != "w").mkString("\n"))

abstract class Token extends Serializable
case object T_SEMI extends Token
case class T_LPAREN(s: String) extends Token
case class T_RPAREN(s: String) extends Token
case class T_ID(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_KWD(s: String) extends Token
case class T_STR(s: String) extends Token

// transforms pairs into tokens
val token : PartialFunction[(String, String), Token] = {
  case ("s", _) => T_SEMI
  case ("lp", s) => T_LPAREN(s)
  case ("rp", s) => T_RPAREN(s)
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("k", s) => T_KWD(s)
  case ("str", s) => T_STR(s)
}

def tokenise(s: String) : List[Token] =
  lexing_simp(WHILE_REGS, s).collect(token)


// A parser and interpreter for the While language
//

import scala.language.implicitConversions
import scala.language.reflectiveCalls

// more convenience for the semantic actions later on
case class ~[+A, +B](_1: A, _2: B)

type IsSeq[A] = A => Seq[_]

abstract class Parser[I: IsSeq, T] {
  def parse(ts: I): Set[(T, I)]

  def parse_all(ts: I): Set[T] =
    for ((head, tail) <- parse(ts); if tail.isEmpty) yield head
}

class SeqParser[I: IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S])
  extends Parser[I, ~[T, S]] {
  def parse(sb: I) =
    for ((head1, tail1) <- p.parse(sb);
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I: IsSeq, T](p: => Parser[I, T], q: => Parser[I, T])
  extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)
}

class FunParser[I: IsSeq, T, S](p: => Parser[I, T], f: T => S)
  extends Parser[I, S] {
  def parse(sb: I) =
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

case class StringParser(s: String) extends Parser[String, String] {
  def parse(sb: String) = {
    val (prefix, suffix) = sb.splitAt(s.length)
    if (prefix == s) Set((prefix, suffix)) else Set()
  }
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(sb: List[Token]) = sb match {
    case T_NUM(n)::rest => Set((n,rest))
    case _ => Set()
  }
}

implicit def string2parser(s: String) = StringParser(s)

implicit def ParserOps[I: IsSeq, T](p: Parser[I, T]) = new {
  def ||(q: => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S](f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S](q: => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

implicit def StringOps(s: String) = new {
  def ||(q: => Parser[String, String]) = new AltParser[String, String](s, q)
  def ||(r: String) = new AltParser[String, String](s, r)
  def ==>[S](f: => String => S) = new FunParser[String, String, S](s, f)
  def ~[S](q: => Parser[String, S]) =
    new SeqParser[String, String, S](s, q)
  def ~(r: String) =
    new SeqParser[String, String, String](s, r)
}


// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(w: Words) extends Stmt
case class Read(w: Words) extends Stmt
case class For(s: String, a1: AExp, a2: AExp, bl: Block) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp

case object IdParser extends Parser[List[Token], String] {
  def parse(sb: List[Token]) = sb match {
    case T_ID(s)::rest => Set((s,rest))
    case _ => Set()
  }
}

case object OpParser extends Parser[List[Token], String] {
  def parse(sb: List[Token]) = sb match {
    case T_OP(s)::rest => Set((s,rest))
    case _ => Set()
  }
}

case object AStringParser extends Parser[List[Token], String] {
  def parse(sb: List[Token]) = sb match {
    case T_STR(s)::rest => Set((s,rest))
    case _ => Set()
  }
}

case class TokenParser(token: Token) extends Parser[List[Token], String] {
  def parse(sb: List[Token]) = sb match {
    case `token` ::rest => token match {
      case T_SEMI => Set((";",rest))
      case T_LPAREN(s) => Set((s,rest))
      case T_RPAREN(s) => Set((s,rest))
      case T_OP(s) => Set((s,rest))
      case T_KWD(s) => Set((s,rest))
      case T_STR(s) => Set((s,rest))
      case _ => Set()
    }
    case _ => Set()
  }
}


abstract class Words
case class Identifier(s: String) extends Words
case class AString(s: String) extends Words
lazy val Writable: Parser[List[Token], Words] =
  (TokenParser(T_LPAREN("(")) ~ Writable ~ TokenParser(T_RPAREN(")"))) ==> { case _ ~ y ~ _ => y } ||
    IdParser ==> Identifier ||
    AStringParser ==> AString
lazy val Readable: Parser[List[Token], Words] =
  (TokenParser(T_LPAREN("(")) ~ Readable ~ TokenParser(T_RPAREN(")"))) ==> { case _ ~ y ~ _ => y } ||
    IdParser ==> Identifier

// arithmetic expressions
lazy val AExp: Parser[List[Token], AExp] =
  (Te ~ TokenParser(T_OP("+")) ~ AExp) ==> { case x ~ _ ~ z   => Aop("+", x, z): AExp } ||
    (Te ~ TokenParser(T_OP("-")) ~ AExp) ==> { case x ~ _ ~ z => Aop("-", x, z): AExp } || Te
lazy val Te: Parser[List[Token], AExp] =
  (Fa ~ TokenParser(T_OP("*")) ~ Te) ==> { case x ~ _ ~ z   => Aop("*", x, z): AExp } ||
    (Fa ~ TokenParser(T_OP("%")) ~ Te) ==> { case x ~ _ ~ z => Aop("%", x, z): AExp } ||
    (Fa ~ TokenParser(T_OP("/")) ~ Te) ==> { case x ~ _ ~ z => Aop("/", x, z): AExp } || Fa
lazy val Fa: Parser[List[Token], AExp] =
  (TokenParser(T_LPAREN("(")) ~ AExp ~ TokenParser(T_RPAREN(")"))) ==> { case _ ~ y ~ _ => y } ||
    IdParser ==> Var ||
    NumParser ==> Num

// boolean expressions with some simple nesting
lazy val BExp: Parser[List[Token], BExp] =
  (AExp ~ TokenParser(T_OP("==")) ~ AExp) ==> { case x ~ _ ~ z   => Bop("==", x, z): BExp } ||
    (AExp ~ TokenParser(T_OP("!=")) ~ AExp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } ||
    (AExp ~ TokenParser(T_OP("<")) ~ AExp) ==> { case x ~ _ ~ z  => Bop("<", x, z): BExp } ||
    (AExp ~ TokenParser(T_OP(">")) ~ AExp) ==> { case x ~ _ ~ z  => Bop(">", x, z): BExp } ||
    (TokenParser(T_LPAREN("(")) ~ BExp ~ TokenParser(T_RPAREN(")")) ~ TokenParser(T_OP("&&")) ~ BExp) ==> {
      case _ ~ y ~ _ ~ _ ~ v => And(y, v): BExp
    } ||
    (TokenParser(T_LPAREN("(")) ~ BExp ~ TokenParser(T_RPAREN(")")) ~ TokenParser(T_OP("||")) ~ BExp) ==> {
      case _ ~ y ~ _ ~ _ ~ v => Or(y, v): BExp
    } ||
    (TokenParser(T_KWD("true")) ==> (_ => True: BExp)) ||
    (TokenParser(T_KWD("false")) ==> (_ => False: BExp)) ||
    (TokenParser(T_LPAREN("(")) ~ BExp ~ TokenParser(T_RPAREN(")"))) ==> { case _ ~ x ~ _ => x }


// statement / statements
lazy val Stmt: Parser[List[Token], Stmt] =
  (TokenParser(T_KWD("skip")) ==> (_ => Skip: Stmt)) ||
    (IdParser ~ TokenParser(T_OP(":=")) ~ AExp) ==> { case x ~ _ ~ z    => Assign(x, z): Stmt } ||
    (TokenParser(T_KWD("write")) ~ Writable) ==> { case _ ~ y => Write(y): Stmt } ||
    (TokenParser(T_KWD("read")) ~ Readable) ==> { case _ ~ y => Read(y): Stmt } ||
    (TokenParser(T_KWD("if")) ~ BExp ~ TokenParser(T_KWD("then")) ~ Block ~ TokenParser(T_KWD("else")) ~ Block) ==> {
      case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w): Stmt
    } ||
    (TokenParser(T_KWD("while")) ~  BExp ~ TokenParser(T_KWD("do")) ~ Block) ==> { case _ ~ y ~ _ ~ w => While(y, w)} ||
    (TokenParser(T_KWD("for")) ~  IdParser ~ TokenParser(T_OP(":=")) ~ AExp ~ TokenParser(T_KWD("upto"))
      ~ AExp ~ TokenParser(T_KWD("do")) ~ Block) ==> { case _ ~ y ~ _ ~ w ~ _ ~ u ~ _ ~ s => For(y, w,u,s)}

lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ TokenParser(T_SEMI) ~ Stmts) ==> { case x ~ _ ~ z => x :: z: Block } ||
    (Stmt ==> (s => List(s): Block))

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  (TokenParser(T_LPAREN("{")) ~ Stmts ~ TokenParser(T_RPAREN("}"))) ==> { case _ ~ y ~ _ => y } ||
    (Stmt ==> (s => List(s)))

Stmts.parse_all(tokenise("x2:=5+3;"))
Stmts.parse_all(tokenise("while 3<x do {x:=2}"))
Stmts.parse_all(tokenise("write ((hello))"))
Stmts.parse_all(tokenise("write (hello)"))
Stmts.parse_all(tokenise("write hello"))
Stmts.parse_all(tokenise("if (a < b) then skip else a := a * b + 1 "))
Stmts.parse_all(tokenise("if((x==2)&&y==3)then{x:=4;y:=2}else{x:=2;y:=3}"))
Block.parse_all(tokenise("{x:=5;y:=8}"))
Block.parse_all(tokenise("if(false)then{x:=5}else{x:=10}"))


val fib = """n := 10;
             minus1 := 0;
             minus2 := 1;
             temp := 0;
             while (n > 0) do {
                 temp := minus2;
                 minus2 := minus1 + minus2;
                 minus1 := temp;
                 n := n - 1
             };
             result := minus2""".replaceAll("\\s+", "")

Stmts.parse_all(tokenise(fib))

// an interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env): Int = a match {
  case Num(i)           => i
  case Var(s)           => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env): Boolean = b match {
  case True              => true
  case False             => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2)  => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2)  => eval_aexp(a1, env) < eval_aexp(a2, env)
  case And(b1, b2)       => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2)        => eval_bexp(b1, env) || eval_bexp(b2, env)
}

def eval_stmt(s: Stmt, env: Env): Env = s match {
  case Skip         => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) =>
    if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env)
  case While(b, bl) =>
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case Write(x) => x match {
    case AString(str) => println(str.drop(1).dropRight(1)); env
    case Identifier(str) => println(env(str)); env
  }
  case Read(x) => x match {
    case Identifier(str) =>  env + (str -> eval_aexp(AExp.parse_all(tokenise(scala.io.StdIn.readLine())).head, env))
  }
  case For(s,a1,a2,bl) =>
    val newEnv = env + (s -> eval_aexp(a1, env))
    if (!eval_bexp(Bop(">",Num(newEnv(s)),a2),newEnv)) eval_stmt(For(s,Aop("+",a1,Num(1)),a2,bl),eval_bl(bl, newEnv))
    else newEnv
}

def eval_bl(bl: Block, env: Env): Env = bl match {
  case Nil     => env
  case s :: bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block): Env = eval_bl(bl, Map())

// parse + evaluate fib program; then lookup what is
// stored under the variable result
println(eval(Stmts.parse_all(tokenise(fib)).head)("result"))

val fib2 = """write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do
  { temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp; n := n - 1 };
  write "Result";
  write minus2
"""

println(Stmts.parse_all(tokenise("""write ("Fib")""")))
eval(Stmts.parse_all(tokenise("""write ("Fib")""")).head)
eval(Stmts.parse_all(tokenise(fib2)).head)
// more examples

// calculate and print all factors bigger
// than 1 and smaller than n
println("Factors")

val factors =
  """n := 12;
      f := 2;
      while (f < n / 2 + 1) do {
        if ((n / f) * f == n) then  { write(f) } else { skip };
        f := f + 1
      }"""

eval(Stmts.parse_all(tokenise(factors)).head)

// calculate all prime numbers up to a number
println("Primes")

val primes =
  """end := 100;
      n := 2;
      while (n < end) do {
        f := 2;
        tmp := 0;
        while ((f < n / 2 + 1) && (tmp == 0)) do {
          if ((n / f) * f == n) then  { tmp := 1 } else { skip };
          f := f + 1
        };
        if (tmp == 0) then { write(n) } else { skip };
        n  := n + 1
      }"""

eval(Stmts.parse_all(tokenise(primes)).head)

val loop =
  """start := 650;
     x := start;
     y := start;
     z := start;
     while 0 < x do {
      while 0 < y do {
        while 0 < z do {
          z := z - 1
        };
        z := start;
        y := y - 1
      };
      y := start;
      x := x - 1
     }
"""
Stmts.parse_all(tokenise(loop))

val forTest = """for i := 2 upto 4 do {
  write i }
  """
Stmts.parse_all(tokenise(forTest))
eval(Stmts.parse_all(tokenise(forTest)).head)


// compiler headers needed for the JVM
// (contains methods for read and write)
val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V
    .limit locals 1
    .limit stack 2
    getstatic java/lang/System/out Ljava/io/PrintStream;
    iload 0
    invokevirtual java/io/PrintStream/println(I)V
    return
.end method

.method public static writes(Ljava/lang/String;)V
 .limit stack 2
 .limit locals 1
 getstatic java/lang/System/out Ljava/io/PrintStream;
 aload 0
 invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
 return
 .end method


.method public static read()I
    .limit locals 10
    .limit stack 10

    ldc 0
    istore 1  ; this will hold our final integer
Label1:
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I
    istore 2
    iload 2
    ldc 10   ; the newline delimiter
    isub
    ifeq Label2
    iload 2
    ldc 32   ; the space delimiter
    isub
    ifeq Label2

    iload 2
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48
    isub
    ldc 10
    iload 1
    imul
    iadd
    istore 1
    goto Label1
Label2:
    ;when we come here we have our integer computed in local variable 1
    iload 1
    ireturn
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""

// Compiler functions


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// convenient string interpolations
// for instructions and labels
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

// this allows you to write things like
// i"add" and l"Label"




def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
  case "/" => i"idiv"
  case "%" => i"irem"
}

// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}


// boolean expression compilation
//  - the jump-label is for where to jump if the condition is not true
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop(">", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmple $jmp"
  case And(b1, b2) =>
    compile_bexp(b1, env, jmp) ++ compile_bexp(b2, env, jmp)
}

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  }
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case Write(x) => x match {
    case AString(str) =>
      (i"ldc $str \t\t; $str" ++
        i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V", env)
    case Identifier(str) =>
      (i"iload ${env(str)} \t\t; $str" ++
        i"invokestatic XXX/XXX/write(I)V", env)
  }
  case Read(Identifier(str)) => {
    val index = env.getOrElse(str, env.keys.size)
    (i"invokestatic XXX/XXX/read()I" ++
     i"istore $index \t\t; $str", env + (str -> index))
  }
  case For(s,a1,a2,bl1) => {
    val loop_begin = Fresh("Loop_begin")
    val bl2 = bl1 :+ Assign(s,Aop("+",Var(s),Num(1)))
    val (instrs1,env1) = compile_stmt(Assign(s,a1),env)
    val (instrs2,env2) = compile_stmt(While(Bop("<",Var(s),Aop("+",a2,Num(1))),bl2),env1)
    (instrs1 ++
      instrs2, env2
      )

  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}


// compiling and running files
//
// JVM files can be assembled with
//
//    java -jar jvm/jasmin-2.4/jasmin.jar fib.j
//
// and started with
//
//    java fib/fib



import scala.util._
import scala.sys.process._
import scala.io

def compile_tofile(bl: Block, class_name: String) = {
  val output = compile(bl, class_name)
  val fw = new java.io.FileWriter(class_name + ".j")
  fw.write(output)
  fw.close()
}

def compile_all(bl: Block, class_name: String) : Unit = {
  compile_tofile(bl, class_name)
  println("compiled ")
  val test = ("java -jar jvm/jasmin-2.4/jasmin.jar " + class_name + ".j").!!
  println("assembled ")
}

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


def compile_run(bl: Block, class_name: String) : Unit = {
  println("Start compilation")
  compile_all(bl, class_name)
  println("running")
  println("Time: " + time_needed(1, ("java " + class_name + "/" + class_name).!))
}

// Fibonacci numbers as a bare-bone test-case
val fib_test = 
  List(Assign("n", Num(9)),            //  n := 10;                     
       Assign("minus1",Num(0)),         //  minus1 := 0;
       Assign("minus2",Num(1)),         //  minus2 := 1;
       Assign("temp",Num(0)),           //  temp := 0;
       While(Bop("<",Num(0),Var("n")),  //  while n > 0 do  {
          List(Assign("temp",Var("minus2")), //  temp := minus2;
               Assign("minus2",Aop("+",Var("minus1"),Var("minus2"))), 
                                        //  minus2 := minus1 + minus2;
               Assign("minus1",Var("temp")), //  minus1 := temp;
               Assign("n",Aop("-",Var("n"),Num(1))))), //  n := n - 1 };
       Write(Identifier("minus1")))                 //  write minus1

compile_run(fib_test, "fib")
// the compiled file as string
//
//println(compile(fib_test, "fib"))
val fib3 = """
write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do
  { temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp; n := n - 1 };
write "Result";
  write minus2
"""

compile_run(Stmts.parse_all(tokenise(forTest)).head, "forTest")
//compile_run(Stmts.parse_all(tokenise(fib3)).head, "fib3")

val for2 = """
for i := 1 upto 10 do {
  for i := 1 upto 10 do {
    write i } }
    """
compile_run(Stmts.parse_all(tokenise(for2)).head, "for2")



val readTest = """read n; write n"""
compile_run(Stmts.parse_all(tokenise(readTest)).head, "readTest")
val fact =
  """write "Fact";
    |read n;
    |result := 1;
    |while n > 0 do {
    |result := result * n;
    |n := n - 1
    |};
    |write "Result";
    |write result
  """.stripMargin
compile_run(Stmts.parse_all(tokenise(fact)).head, "fact")

