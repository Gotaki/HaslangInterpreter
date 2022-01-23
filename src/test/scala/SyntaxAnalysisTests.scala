/**
 * HasLang syntax analysis tests.
 *
 * Copyright 2021, Anthony Sloane, Matthew Roberts, Kym Haines, Macquarie University, All rights reserved.
 */

package haslang

import org.bitbucket.inkytonik.kiama.util.ParseTests
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

/**
 * Tests that check that the syntax analyser works correctly.  I.e., it accepts
 * correct input and produces the appropriate trees, and it rejects illegal input.
 */
@RunWith(classOf[JUnitRunner])
class SyntaxAnalysisTests extends ParseTests {

    import HasLangTree._

    val parsers = new SyntaxAnalysis (positions)
    import parsers._

    // Tests of parsing basic expressions

    test ("equal expression") {
        exp ("a == 1") should parseTo[HasLangNode] (EqualExp (IdnUse ("a"), IntExp (1)))
    }

    test ("less than expression") {
        exp ("a < 1") should parseTo[HasLangNode] (LessExp (IdnUse ("a"), IntExp (1)))
    }

    test ("addition expression") {
        exp ("a + 1") should parseTo[HasLangNode] (PlusExp (IdnUse ("a"), IntExp (1)))
    }

    test ("subtraction expression") {
        exp ("a - 1") should parseTo[HasLangNode] (MinusExp (IdnUse ("a"), IntExp (1)))
    }

    test ("multiplication expression") {
        exp ("a * 1") should parseTo[HasLangNode] (StarExp (IdnUse ("a"), IntExp (1)))
    }

    test ("division expression") {
        exp ("a / 1") should parseTo[HasLangNode] (SlashExp (IdnUse ("a"), IntExp (1)))
    }

    test ("integer expression") {
        exp ("823") should parseTo[HasLangNode] (IntExp (823))
    }

    test ("true expression") {
        exp ("true") should parseTo[HasLangNode] (BoolExp (true))
    }

    test ("false expression") {
        exp ("false") should parseTo[HasLangNode] (BoolExp (false))
    }

    test ("identifier expression") {
        exp ("v123") should parseTo[HasLangNode] (IdnUse ("v123"))
    }

    test ("parenthesized expression") {
        exp ("(a + 5)") should parseTo[HasLangNode] (PlusExp (IdnUse ("a"), IntExp (5)))
    }

    test ("application expression 1") {
        exp ("a b") should parseTo[HasLangNode] (AppExp (IdnUse ("a"), IdnUse ("b")))
    }

    test ("expression containing an application expression") {
        exp ("1 + foo 2") should parseTo[HasLangNode] (PlusExp(IntExp(1), AppExp (IdnUse ("foo"), IntExp (2))))
    }

    test ("if expression") {
        exp ("if (true) then 3 else 4") should parseTo[HasLangNode] (IfExp (BoolExp (true), IntExp (3), IntExp (4)))
    }

    test ("lambda expression") {
        exp ("\\a :: Int -> a + 1") should parseTo[Exp] (LamExp(
                            IdnDef("a", IntType()),
                            PlusExp(IdnUse("a"), IntExp(1))))
    }

    test ("basic type") {
        tipe ("Bool") should parseTo[Type] (BoolType())
    }

    test ("parsing unit type") {
        tipe ("()") should parseTo[Type] (UnitType())
    }

    test ("parsing list type") {
        tipe ("[Int]") should parseTo[Type] (ListType(IntType()))
    }

    test ("parsing tuple type") {
        tipe ("(Int,Bool,[Bool])") should parseTo[Type] (TupleType(Vector(IntType(), BoolType(), ListType(BoolType()))))
    }

    test ("parsing function type") {
      tipe ("Int->Bool->[Int]") should parseTo[Type] (FunType(IntType(), FunType(BoolType(), ListType(IntType()))))
    }

    test ("parsing bracketted function type") {
      tipe ("(Int->Bool)->[Int]") should parseTo[Type] (FunType(FunType(IntType(), BoolType()), ListType(IntType())))
    }

    test ("empty list") {
        exp ("[]") should parseTo[HasLangNode] (ListExp (Vector()))
    }

    test ("cons expression") {
        exp ("3 : []") should parseTo[HasLangNode] (ConsExp (IntExp (3), ListExp (Vector())))
    }

    test ("list expression") {
        exp ("[3, 4, 5]") should parseTo[HasLangNode] (ListExp (Vector(IntExp(3), IntExp(4), IntExp(5))))
    }

    test ("tuple expression") {
        exp ("(3, 4, 5)") should parseTo[HasLangNode] (TupleExp (Vector(IntExp(3), IntExp(4), IntExp(5))))
    }

    test ("underscore pattern") {
        pat ("_") should parseTo[Pat] (AnyPat())
    }

    test ("literal pattern") {
        pat ("3") should parseTo[Pat] (LiteralPat(IntExp(3)))
    }

    test ("list pattern") {
        pat ("[3, _, 5]") should parseTo[Pat] (ListPat(Vector(LiteralPat(IntExp(3)), AnyPat(), LiteralPat(IntExp(5)))))
    }

    test ("cons pattern") {
        pat ("3 : []") should parseTo[Pat] (ConsPat(LiteralPat(IntExp(3)), ListPat(Vector())))
    }

    test ("tuple pattern") {
        pat ("(3, _, 5)") should parseTo[Pat] (TuplePat(Vector(LiteralPat(IntExp(3)), AnyPat(), LiteralPat(IntExp(5)))))
    }

    test ("simple function line") {
        funline ("fac 0 = 1") should parseTo[FunLine] (FunLine("fac", Vector(LiteralPat(IntExp(0))), IntExp(1)))
    }

    test ("more complicated function line") {
        funline ("length h:t = 1 + length t") should parseTo[FunLine] (FunLine("length", Vector(ConsPat(IdentPat("h"), IdentPat("t"))), PlusExp(IntExp(1), AppExp(IdnUse("length"), IdnUse("t")))))
    }

    test ("simple variable") {
        defn ("x :: Int = 100") should parseTo[Defn] (Defn(IdnDef("x", IntType()), Vector(FunLine("", Vector(), IntExp(100)))))
    }

    test ("function with two lines") {
      defn ("""inc :: Int -> Int
               inc n = n + 1
            """) should parseTo[Defn] (Defn(
                  IdnDef("inc", FunType(IntType(), IntType())),
                  Vector(FunLine("inc", Vector(IdentPat("n")),
                                 PlusExp(IdnUse("n"), IntExp(1))))))
    }

    test ("function with three lines") {
      defn ("""fac :: Int -> Int
               fac 0 = 1.
               fac n = n * fac (n - 1)
            """) should parseTo[Defn] (Defn(
                  IdnDef("fac", FunType(IntType(), IntType())),
                  Vector(FunLine("fac", Vector(LiteralPat(IntExp(0))),
                                 IntExp(1)),
                         FunLine("fac", Vector(IdentPat("n")),
                                 StarExp(IdnUse("n"),
                                         AppExp(IdnUse("fac"),
                                                MinusExp(IdnUse("n"),
                                                         IntExp(1))))))))
    }

    test ("one definition") {
      definitions ("""x   :: Int        = 100
                """) should parseTo[Vector[Defn]] (Vector(Defn(
                            IdnDef("x", IntType()),
                            Vector(FunLine("", Vector(), IntExp(100))))))
    }

    test ("one definition with lambda") {
      definitions ("""inc :: Int -> Int = \a :: Int -> a + 1
                """) should parseTo[Vector[Defn]] (Vector(Defn(
                            IdnDef("inc", FunType(IntType(), IntType())),
                            Vector(FunLine("", Vector(), LamExp(
                                              IdnDef("a", IntType()),
                                              PlusExp(IdnUse("a"), IntExp(1)))))
                                        )))
    }

    test ("two definitions") {
      definitions ("""x   :: Int        = 100;
                      y   :: Bool       = false
                """) should parseTo[Vector[Defn]] (Vector(
                       Defn(IdnDef("x", IntType()),
                            Vector(FunLine("", Vector(), IntExp(100)))),
                       Defn(IdnDef("y", BoolType()),
                            Vector(FunLine("", Vector(), BoolExp(false))))))
    }

    test ("let with one definition") {
      program ("""let
                    x   :: Int        = 100
                  in
                    inc x
                """) should parseTo[Program] (Program(LetExp(
                    Vector(Defn(
                            IdnDef("x", IntType()),
                            Vector(FunLine("", Vector(), IntExp(100))))),
                    AppExp (IdnUse ("inc"), IdnUse ("x")))))
    }

    test ("let with two definitions") {
      program ("""let
                    x   :: Int        = 100;
                    y   :: Bool       = false
                  in
                    inc x
                """) should parseTo[Program] (Program(LetExp(
                    Vector(Defn(
                             IdnDef("x", IntType()),
                             Vector(FunLine("", Vector(), IntExp(100)))),
                           Defn(
                             IdnDef("y", BoolType()),
                             Vector(FunLine("", Vector(), BoolExp(false))))),
                    AppExp (IdnUse ("inc"), IdnUse ("x")))))
    }

    test ("program with two definitions including lambda") {
      program ("""let
                    x   :: Int        = 100;
                    inc :: Int -> Int = \a :: Int -> a + 1
                  in
                    inc x
                """) should parseTo[Program] (Program(LetExp(
                    Vector(Defn(
                            IdnDef("x", IntType()),
                            Vector(FunLine("", Vector(), IntExp(100)))),
                           Defn(
                            IdnDef("inc", FunType(IntType(), IntType())),
                            Vector(FunLine("", Vector(), LamExp(
                                              IdnDef("a", IntType()),
                                              PlusExp(IdnUse("a"), IntExp(1)))))
                                        )),
                    AppExp (IdnUse ("inc"), IdnUse ("x")))))
    }

    test ("program with definitions including lambda and multiline fun") {
      program ("""let
                    x   :: Int        = 100;
                    inc :: Int -> Int = \a :: Int -> a + 1;
                    length :: [Int] -> Int
                    length [] = 0.
                    length h:t = 1 + length t
                  in
                    inc x
                """) should parseTo[Program] (Program(LetExp(
                    Vector(Defn(
                            IdnDef("x", IntType()),
                            Vector(FunLine("", Vector(), IntExp(100)))),
                           Defn(
                            IdnDef("inc", FunType(IntType(), IntType())),
                            Vector(FunLine("", Vector(), LamExp(
                                            IdnDef("a", IntType()),
                                            PlusExp(IdnUse("a"), IntExp(1)))))),
                           Defn(
                            IdnDef("length", FunType(ListType(IntType()),
                                                     IntType())),
                            Vector(FunLine("length", Vector(ListPat(Vector())),
                                           IntExp(0)),
                                   FunLine("length",
                                           Vector(ConsPat(IdentPat("h"),
                                                          IdentPat("t"))),
                                           PlusExp(IntExp(1),
                                                   AppExp(IdnUse("length"),
                                                          IdnUse("t")))))
                                        )),
                     AppExp (IdnUse ("inc"), IdnUse ("x")))))
    }

    // FIXME: more tests here...
    test ("multiplication expression 2") {
        exp ("b * 54") should parseTo[HasLangNode] (StarExp (IdnUse ("b"), IntExp (54)))
    }

    test ("parenthesized expression") {
        exp ("(a + (b-c))") should parseTo[HasLangNode] (PlusExp (IdnUse ("a"), (MinusExp (IdnUse ("b"), IdnUse ("c")))))
    }
    
    test ("expression containing an application expression (Subtraction)") {
        exp ("1 - foo 2") should parseTo[HasLangNode] (MinusExp(IntExp(1), AppExp (IdnUse ("foo"), IntExp(2))))
    }
    test ("expression containing an application expression (Multiplication)") {
        exp ("1 * foo 2") should parseTo[HasLangNode] (StarExp(IntExp(1), AppExp (IdnUse ("foo"), IntExp(2))))
    }
    test ("expression containing an application expression (Division)") {
        exp ("1 / foo 2") should parseTo[HasLangNode] (SlashExp(IntExp(1), AppExp (IdnUse ("foo"), IntExp(2))))
    }

     test ("identifier expression 2") {
        exp ("Victor123C") should parseTo[HasLangNode] (IdnUse ("Victor123C"))
    }

    test ("list expression 2") {
        exp ("[4, 6, 8]") should parseTo[HasLangNode] (ListExp (Vector(IntExp(4), IntExp(6), IntExp(8))))
    }

    test ("list within a list") {
        exp ("[4, 6, [4, 6]]") should parseTo[HasLangNode] (ListExp (Vector(IntExp(4), IntExp(6), ListExp (Vector(IntExp(4), IntExp(6))))))
    }

    test ("tuple  within a tuple ") {
        exp ("(3, 4, (3,4))") should parseTo[HasLangNode] (TupleExp (Vector(IntExp(3), IntExp(4), TupleExp (Vector(IntExp(3), IntExp(4))))))
    }

    test ("lambda expression 2") {
        exp ("\\b :: Bool -> b + 9") should parseTo[Exp] (LamExp(
                            IdnDef("b", BoolType()),
                            PlusExp(IdnUse("b"), IntExp(9))))
    }

    test ("parsing tuple type 2") {
        tipe ("(Int,Int,[Int])") should parseTo[Type] (TupleType(Vector(IntType(), IntType(), ListType(IntType()))))
    }

    test ("simple function line 2") {
        funline ("test 99 = 100") should parseTo[FunLine] (FunLine("test", Vector(LiteralPat(IntExp(99))), IntExp(100)))
    }

    test ("more complicated function line (Subtraction)") {
        funline ("size a:b = 1 - size b") should parseTo[FunLine] (FunLine("size", Vector(ConsPat(IdentPat("a"), IdentPat("b"))), MinusExp(IntExp(1), AppExp(IdnUse("size"), IdnUse("b")))))
    }
    
    test ("one definition 2") {
      definitions ("""x   :: Bool        = 100
                """) should parseTo[Vector[Defn]] (Vector(Defn(
                            IdnDef("x", BoolType()),
                            Vector(FunLine("", Vector(), IntExp(100))))))
    }

    test ("let with two int definitions") {
      program ("""let
                    x   :: Int        = 100;
                    y   :: Int       = 101
                  in
                    inc y
                """) should parseTo[Program] (Program(LetExp(
                    Vector(Defn(
                             IdnDef("x", IntType()),
                             Vector(FunLine("", Vector(), IntExp(100)))),
                           Defn(
                             IdnDef("y", IntType()),
                             Vector(FunLine("", Vector(), IntExp(101))))),
                    AppExp (IdnUse ("inc"), IdnUse ("y")))))
    }
    
}
