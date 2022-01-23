/**
 * HasLang syntax analyser.
 *
 * Copyright 2021, Anthony Sloane, Matthew Roberts, Kym Haines, Macquarie University, All rights reserved.
 */

package haslang

import org.bitbucket.inkytonik.kiama.parsing.Parsers
import org.bitbucket.inkytonik.kiama.util.Positions
import scala.reflect.internal.util.TraceSymbolActivity
import java.util.ListIterator
import javax.naming.PartialResultException

/**
 * Module containing parsers for HasLang.
 */
class SyntaxAnalysis (positions : Positions) extends Parsers (positions) {

    import HasLangTree._
    import scala.language.postfixOps

    lazy val parser : PackratParser[Program] =
        phrase (program)

    lazy val program : PackratParser[Program] =
        exp ^^ Program

    lazy val lam : PackratParser[LamExp] = 
        ("\\" ~> idndef) ~ ("->" ~> exp) ^^ {case idn ~ body => LamExp(idn, body)}

    lazy val literal : PackratParser[Exp] =
        "false" ^^^ BoolExp (false) |
        "true" ^^^ BoolExp (true) |
        integer ^^ (s => IntExp (s.toInt)) 
  
    //Level 0 Precedence (Conditional Expressions [If Expressions])
    lazy val exp : PackratParser[Exp] = //left associative, goto exp1
        condExp |
        exp1

    //Level 1 Predence (Let Expressions)
    lazy val exp1 : PackratParser[Exp] = //left associative, goto exp2
        letExp |
        exp2

    //Level 2 Precedence (App Expressions)
    lazy val exp2 : PackratParser[Exp] =   //left associative, goto exp3
        appExp |
        exp3

    //Level 3 Precendence (Equal and Less than)
    lazy val exp3 : PackratParser[Exp] = //not associative
        exp4 ~ ("==" ~> factor) ^^ {case e ~ f => EqualExp(e, f)} | 
        exp4 ~ ("<" ~> factor) ^^ {case e ~ f => LessExp(e, f)} |
        exp4

    //Level 4 Precendence (Addition and Subtraction)
    lazy val exp4 : PackratParser[Exp] =
        exp4 ~ ("+" ~> factor) ^^ {case e ~ f => PlusExp(e, f)} |
        exp4 ~ ("-" ~> factor) ^^ {case e ~ f => MinusExp(e, f)} |
        exp5
    
    //Level 5 Precedence (Multiplication and Division)
    lazy val exp5 : PackratParser[Exp] =
        exp5 ~ ("*" ~> factor) ^^ {case e ~ f => StarExp(e, f)} | 
        exp5 ~ ("/" ~> factor) ^^ {case e ~ f => SlashExp(e, f)} |  
        exp6

    //Level 6 Precedence (Cons Expression)
    lazy val exp6 : PackratParser[Exp] =
        exp6 ~ (":" ~> factor) ^^ {case e ~ f => ConsExp(e, f)} |
        exp7

    //Level 7 Precedence (Expression containing an application expression)
    lazy val exp7 : PackratParser[Exp] =    
        identifier ^^ {case e => IdnUse(e)} |
        exp8

    //Level 8 Precedence (List Expressions)
    lazy val exp8 : PackratParser[Exp] =
        listExp |
        factor  
    
    //Level 9 Precedence (Other Expressions)
    lazy val factor : PackratParser[Exp] =
        lam |
        literal |
        exp |
        identifier ^^ IdnUse |
        "(" ~> exp <~ ")" |
        tupleExp | 
        failure ("exp expected")

    lazy val appExp : PackratParser[AppExp] =
        exp6 ~ factor ^^ {case e ~ f => AppExp(e, f)}

    lazy val condExp : PackratParser[IfExp] = 
        //condition: "if" "(" literal ")" "then" exp "else" exp
        ("if" ~> "(" ~> literal <~ ")") ~ ("then" ~> exp) ~ ("else" ~> exp) ^^ {case l ~ r ~ w => IfExp(l, r, w)} 

    lazy val tupleExp : PackratParser[TupleExp] =
        //"(" 
        "(" ~> (rep1sep(factor, ",")) <~ ")" ^^ {case t => TupleExp(t)} 

    lazy val letExp : PackratParser[LetExp] = 
        ("let" ~> definitions) ~ ("in" ~> exp) ^^ {case l ~ r => LetExp(l, r)}

    lazy val listExp : PackratParser[ListExp] = 
        "[" ~ "]" ^^^ ListExp(Vector()) | 
        "[" ~> repsep(factor, ",") <~ "]" ^^ {case t => ListExp(t)}

    lazy val definitions : PackratParser[Vector[Defn]] =
        rep1sep(defn, ";") ^^ Vector[Defn]

    lazy val defn : PackratParser[Defn] =
        idndef ~ rep1sep(funline, ".") ^^ Defn

    lazy val funline : PackratParser[FunLine] =
       (identifier?) ~ ((pat*) <~ "=") ~ exp ^^ {case id ~ pat ~ exp => {
            id match {
                case None => FunLine("", pat, exp)
                case _ => FunLine(id.get, pat, exp)
            }
        }}

    lazy val pat : PackratParser[Pat] =
        basicpat ~ (":" ~> pat) ^^ {case l ~ r => ConsPat(l, r)} |
        "[" ~> repsep(pat, ",") <~ "]" ^^ {case t => ListPat(t)} | 
        "(" ~> rep1sep(pat, ",") <~ ")" ^^ {case t => TuplePat(t)} |
        basicpat

    lazy val basicpat : PackratParser[Pat] =
        literal ^^ LiteralPat |
        "_" ^^^ AnyPat() | 
        identifier ^^ IdentPat |
        "(" ~> pat <~ ")"

    lazy val tipe : PackratParser[Type] =
        tipe ~ ("->" ~> tipe) ^^ {case tipe1 ~ tipe2 => FunType(tipe1,tipe2)} |
        ("[" ~> tipe <~ "]") ^^ {case t => ListType(t)} |
        basictipe | 
        "(" ~> rep1sep(tipe, ",") <~ ")" ^^ {case t => TupleType(t)} 
        
    lazy val basictipe : PackratParser[Type] =
        "Int" ^^^ IntType() |
        "Bool" ^^^ BoolType() |
        "(" ~ ")" ^^^ UnitType() |
        "(" ~> tipe <~ ")" 

    // NOTE: You should not change anything below here...

    lazy val integer =
        regex ("[0-9]+".r)

    lazy val idndef =
        (identifier <~ "::") ~ tipe ^^ IdnDef

    val keywordStrings =
        List ("let", "else", "false", "if", "then", "true", "in")

    lazy val keyword =
        keywords ("[^a-zA-Z0-9_]".r, keywordStrings)

    lazy val identifier =
        not (keyword) ~> identifierBase

    lazy val identifierBase =
        regex ("[a-zA-Z][a-zA-Z0-9_]*".r) |
        failure ("identifier expected")

    lazy val whitespaceParser : PackratParser[Any] =
        rep ( """\s""".r | comment)

    lazy val comment : PackratParser[Any] =
        "{-" ~ rep (not ("-}") ~ (comment | any)) ~ "-}" |
        "--.*(\n|\\z)".r

}
