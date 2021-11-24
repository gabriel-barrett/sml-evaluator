type def_idx = int
type env_idx = int

datatype term =
         TVAR of env_idx
         | TLAM of term
         | TAPP of term * term
         | TREF of def_idx
         | TINT of int
         | TADD of env_idx * env_idx
         | TMUL of env_idx * env_idx
         | TSUB of env_idx * env_idx
         | TEQZ of env_idx * term * term

datatype value =
         VNEU of neutral
         | VAPP of neutral * value list
         | VLAM of term * value list
     and neutral =
         NVAR of int
         | NINT of int
         | NADD of value * value
         | NMUL of value * value
         | NSUB of value * value
         | NEQZ of value * value list * term * term

fun papp (neu, args) = if null args then VNEU neu else VAPP (neu, args)

fun eval (defs, trm, env, args) =
    case trm of
        TAPP (func, arg) =>
        let val arg = eval(defs, arg, env, [])
        in eval (defs, func, env, arg :: args) end
      | TLAM bod => (case args of
                        (arg :: args) => eval (defs, bod, arg :: env, args)
                      | [] => VLAM (bod, env))
      | TVAR idx => apply (defs, List.nth (env, idx), args)
      | TREF idx => eval (defs, Vector.sub (defs, idx), [], args)
      | TINT num => papp (NINT num, args)
      | TADD (idx1, idx2) =>
        let
            val value1 = List.nth (env, idx1)
            val value2 = List.nth (env, idx2)
        in
            (case (value1, value2) of
                 (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a+b), args)
               | _ => papp (NADD (value1, value2), args))
        end
      | TMUL (idx1, idx2) =>
        let
            val value1 = List.nth (env, idx1)
            val value2 = List.nth (env, idx2)
        in
            (case (value1, value2) of
                 (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a*b), args)
               | _ => papp (NMUL (value1, value2), args))
        end
      | TSUB (idx1, idx2) =>
        let
            val value1 = List.nth (env, idx1)
            val value2 = List.nth (env, idx2)
        in
            (case (value1, value2) of
                 (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a-b), args)
               | _ => papp (NSUB (value1, value2), args))
        end
      | TEQZ (idx, case1, case2) =>
        let
            val value = List.nth (env, idx)
        in
            (case value of
                 VNEU (NINT a) =>
                 if a = 0
                 then eval (defs, case1, env, args)
                 else eval (defs, case2, env, args)
               | _ => papp (NEQZ (value, env, case1, case2), args))
        end
and apply (defs, value, args) =
    if null args then value else
    case value of
        VAPP (neu, args') => VAPP (neu, args' @ args)
      | VNEU neu => VAPP (neu, args)
      | VLAM (trm, env) => eval (defs, trm, List.hd args :: env, List.tl args)

fun printVal t = case t of
                     VNEU (NINT num) => print (Int.toString num ^ "\n")
                   | _ => print "other\n"

(* (* CHURCH ENCODING *) *)
(* (* cons = \x xs n c -> c x (xs n c)*) *)
(* val consT = TLAM (TLAM (TLAM (TLAM (TAPP (TAPP (TVAR 0, TVAR 3), TAPP (TAPP (TVAR 2, TVAR 1), TVAR 0)))))) *)
(* (* nil = \n c -> n*) *)
(* val nilT  = TLAM (TLAM (TVAR 1)) *)
(* (* repeat = \n a -> if n == 0 then nil else cons a (repeat (n-1) a)*) *)
(* val repeatT = TLAM (TLAM (TAPP (TLAM(TEQZ(0, TREF 1, TAPP (TAPP (TREF 0, TVAR 1), TAPP (TAPP (TREF 2, TAPP (TAPP (TREF 9, TVAR 2), TINT 1)), TVAR 1)))), TVAR 1))) *)
(* (* sum = \xs -> xs 0 (\a rec -> ADD a rec)*) *)
(* val sumT = TLAM (TAPP (TAPP (TVAR 0, TINT 0), TLAM (TLAM (TAPP (TAPP (TREF 8, TVAR 1), TVAR 0))))) *)
(* (* map1 = \xs -> xs nil (\a rec -> cons (1 + a) rec) *) *)
(* val map1T = TLAM (TAPP (TAPP (TVAR 0, TREF 1), TLAM (TLAM (TAPP (TAPP (TREF 0, TAPP (TAPP (TREF 8, TVAR 1), TINT 1)), TVAR 0))))) *)

(* SCOTT ENCODING*)
(* cons = \x xs n c -> c x xs*)
val consT = TLAM (TLAM (TLAM (TLAM (TAPP (TAPP (TVAR 0, TVAR 3), TVAR 2)))))
(* nil = \n c -> n*)
val nilT  = TLAM (TLAM (TVAR 1))
(* repeat = \n a -> if n == 0 then nil else cons a (repeat (n-1) a)*)
val repeatT = TLAM (TLAM (TAPP (TLAM (TEQZ (0, TREF 1, TAPP (TAPP (TREF 0, TVAR 1), TAPP (TAPP (TREF 2, TAPP (TAPP (TREF 9, TVAR 2), TINT 1)), TVAR 1)))), TVAR 1)))
(* sum = \xs -> xs 0 (\a as -> ADD a (sum as))*)
val sumT = TLAM (TAPP (TAPP (TVAR 0, TINT 0), TLAM (TLAM (TAPP (TAPP (TREF 8, TVAR 1), TAPP (TREF 3, TVAR 0))))))
(* map1 = \xs -> xs nil (\a as -> cons (1 + a) (map1 as)) *)
val map1T = TLAM (TAPP (TAPP (TVAR 0, TREF 1), TLAM (TLAM (TAPP (TAPP (TREF 0, TAPP (TAPP (TREF 8, TVAR 1), TINT 1)), TAPP (TREF 7, TVAR 0))))))

val addT = TLAM (TLAM (TADD (1, 0)));
val subT = TLAM (TLAM (TSUB (1, 0)));
val valT = TINT 2000000
val listT = TAPP (TAPP (TREF 2, TREF 4), TINT 1)
val mainT = TAPP (TREF 3, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TREF 5))))))))))

val defs = Vector.fromList [consT, nilT, repeatT, sumT, valT, listT, mainT, map1T, addT, subT]
val main = printVal (eval (defs, Vector.sub(defs, 6), [], []))
