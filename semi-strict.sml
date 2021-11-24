datatype primop =
         ADD
         | MUL
         | SUB
         | EQZ

datatype term =
         TVAR of int
         | TLAM of term
         | TAPP of term * term
         | TREF of int
         | TINT of int
         | TOPR of primop

datatype value =
         VNEU of neutral
         | VAPP of neutral * thunk list
         | VLAM of term * value list
     and neutral =
         NVAR of int
         | NINT of int
         | NOPR of primop
     and thunk =
         SUS of term * value list

fun oprArity opr = case opr of
                       ADD => 2
                     | MUL => 2
                     | SUB => 2
                     | EQZ => 3

fun evalArity opr = case opr of
                        ADD => 2
                      | MUL => 2
                      | SUB => 2
                      | EQZ => 1

fun splitAt (ls, n) = let
    fun splitAt' ([], _) = ([], [])
      | splitAt' (x :: xs, 1) = ([x], xs)
      | splitAt' (x :: xs, m) = let
          val (xs', xs'') = splitAt' (xs, m - 1)
      in (x :: xs', xs'') end
    in if n <= 0 then ([], ls) else splitAt' (ls, n) end

exception Impossible
exception TODO

fun papp (neu, args) = if length args > 0 then VAPP (neu, args) else VNEU neu

fun eval (defs, trm, env, args) =
    case trm of
        TAPP (func, arg) =>
        let val thunk = SUS (arg, env)
        in eval (defs, func, env, thunk :: args) end
      | TLAM bod => (case args of
                        (arg :: args) => eval (defs, bod, force (defs, arg) :: env, args)
                      | [] => VLAM (bod, env))
      | TOPR opr => reduceOpr (defs, opr, args)
      | TVAR idx => apply (defs, List.nth (env, idx), args)
      | TINT num => papp (NINT num, args)
      | TREF idx => eval (defs, List.nth (defs, idx), [], args)
and apply (defs, value, args) =
    if length args = 0 then value else
    case value of
        VAPP (NOPR opr, args') => reduceOpr (defs, opr, args' @ args)
      | VAPP (neu, args') => VAPP (neu, args' @ args)
      | VNEU (NOPR opr) => reduceOpr (defs, opr, args)
      | VNEU neu => VAPP (neu, args)
      | VLAM (trm, env) => eval (defs, trm, force (defs, List.hd args) :: env, List.tl args)
and force (defs, thunk) = case thunk of
                              SUS (trm, env) => eval (defs, trm, env, [])
and reduceOpr (defs, opr, args) =
    if length args < oprArity opr
    then papp (NOPR opr, args)
    else
        case opr of
            ADD => reduceAdd (defs, args)
          | MUL => reduceMul (defs, args)
          | SUB => reduceSub (defs, args)
          | EQZ => reduceEqz (defs, args)
and reduceAdd (defs, args) =
    let val (opers, rest) = splitAt (args, 2)
        val oper1 = List.nth (opers, 0)
        val oper2 = List.nth (opers, 1)
    in case (force (defs, oper1), force (defs, oper2)) of
           (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a+b), rest)
         | _ => VAPP (NOPR ADD, args)
    end
and reduceMul (defs, args) =
    let val (opers, rest) = splitAt (args, 2)
        val oper1 = List.nth (opers, 0)
        val oper2 = List.nth (opers, 1)
    in case (force (defs, oper1), force (defs, oper2)) of
           (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a*b), rest)
         | _ => VAPP (NOPR MUL, args)
    end
and reduceSub (defs, args) =
    let val (opers, rest) = splitAt (args, 2)
        val oper1 = List.nth (opers, 0)
        val oper2 = List.nth (opers, 1)
    in case (force (defs, oper1), force (defs, oper2)) of
           (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a-b), rest)
         | _ => VAPP (NOPR SUB, args)
    end
and reduceEqz (defs, args) =
    let val (opers, rest) = splitAt (args, 3)
        val oper1 = List.nth (opers, 0)
    in case force (defs, oper1) of
           VNEU (NINT a) =>
           if a = 0
           then apply (defs, force (defs, List.nth (opers, 1)), rest)
           else apply (defs, force (defs, List.nth (opers, 2)), rest)
         | _ => VAPP (NOPR EQZ, args)
    end
(* and reduceOpr (defs, opr, args) = *)
(*     if length args < oprArity opr then papp (NOPR opr, args) *)
(*     else let *)
(*         val (operands, rest) = splitAt (args, evalArity opr) in *)
(*         case map (fn trm => force (defs, trm)) operands of *)
(*             [VNEU (NINT a), VNEU (NINT b)] => *)
(*             (case opr of *)
(*                  ADD => papp (NINT (a+b), rest) *)
(*                | MUL => papp (NINT (a*b), rest) *)
(*                | SUB => papp (NINT (a-b), rest) *)
(*                | EQZ => raise Impossible) *)
(*            | [VNEU (NINT a)] => *)
(*              (* only eval arity 1 operator is EQZ *) *)
(*              let val (operands, rest) = splitAt (rest, 2) *)
(*              in if a = 0 *)
(*                 then apply (defs, force (defs, List.nth (operands, 0)), rest) *)
(*                 else apply (defs, force (defs, List.nth (operands, 1)), rest) end *)
(*            | _ => papp (NOPR opr, args) end *)


fun printVal t = case t of
                     VNEU (NINT num) => print (Int.toString num ^ "\n")
                   | _ => print "other\n"

(* CHURCH ENCODING *)
(* (* cons = \x xs n c -> c x (xs n c)*) *)
(* val consT = TLAM (TLAM (TLAM (TLAM (TAPP (TAPP (TVAR 0, TVAR 3), TAPP (TAPP (TVAR 2, TVAR 1), TVAR 0)))))) *)
(* (* nil = \n c -> n*) *)
(* val nilT  = TLAM (TLAM (TVAR 1)) *)
(* (* repeat = \n a -> if n == 0 then nil else cons a (repeat (n-1) a)*) *)
(* val repeatT = TLAM (TLAM (TAPP (TAPP (TAPP (TOPR EQZ, TVAR 1), TREF 1), TAPP (TAPP (TREF 0, TVAR 0), TAPP (TAPP (TREF 2, TAPP (TAPP (TOPR SUB, TVAR 1), TINT 1)), TVAR 0))))) *)
(* (* sum = \xs -> xs 0 (\a rec -> ADD a rec)*) *)
(* val sumT = TLAM (TAPP (TAPP (TVAR 0, TINT 0), TLAM (TLAM (TAPP (TAPP (TOPR ADD, TVAR 1), TVAR 0))))) *)
(* (* map1 = \xs -> xs nil (\a rec -> cons (1 + a) rec) *) *)
(* val map1T = TLAM (TAPP (TAPP (TVAR 0, TREF 1), TLAM (TLAM (TAPP (TAPP (TREF 0, TAPP (TAPP (TOPR ADD, TVAR 1), TINT 1)), TVAR 0))))) *)

(* (* SCOTT ENCODING*) *)
(* cons = \x xs n c -> c x xs*)
val consT = TLAM (TLAM (TLAM (TLAM (TAPP (TAPP (TVAR 0, TVAR 3), TVAR 2)))))
(* nil = \n c -> n*)
val nilT  = TLAM (TLAM (TVAR 1))
(* repeat = \n a -> if n == 0 then nil else cons a (repeat (n-1) a)*)
val repeatT = TLAM (TLAM (TAPP (TAPP (TAPP (TOPR EQZ, TVAR 1), TREF 1), TAPP (TAPP (TREF 0, TVAR 0), TAPP (TAPP (TREF 2, TAPP (TAPP (TOPR SUB, TVAR 1), TINT 1)), TVAR 0)))))
(* sum = \xs -> xs 0 (\a as -> ADD a (sum as))*)
val sumT = TLAM (TAPP (TAPP (TVAR 0, TINT 0), TLAM (TLAM (TAPP (TAPP (TOPR ADD, TVAR 1), TAPP (TREF 3, TVAR 0))))))
(* map1 = \xs -> xs nil (\a as -> cons (1 + a) (map1 as)) *)
val map1T = TLAM (TAPP (TAPP (TVAR 0, TREF 1), TLAM (TLAM (TAPP (TAPP (TREF 0, TAPP (TAPP (TOPR ADD, TVAR 1), TINT 1)), TAPP (TREF 7, TVAR 0))))))

val valT = TINT 5000000
val listT = TAPP (TAPP (TREF 2, TREF 4), TINT 1)
val mainT = TAPP (TREF 3, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TREF 5))))))))))

val defs = [consT, nilT, repeatT, sumT, valT, listT, mainT, map1T]
val main = printVal (eval (defs, List.nth(defs, 6), [], []))
