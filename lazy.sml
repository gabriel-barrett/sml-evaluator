datatype term =
         TVAR of int
         | TLAM of term
         | TAPP of term * term
         | TREF of int
         | TINT of int
         | TADD of int * int
         | TMUL of int * int
         | TSUB of int * int
         | TEQZ of int * term * term

datatype value =
         VNEU of neutral
         | VAPP of neutral * thunk ref list
         | VLAM of term * thunk ref list
     and neutral =
         NVAR of int
         | NINT of int
         | NADD of value * value
         | NMUL of value * value
         | NSUB of value * value
         | NEQZ of value * thunk ref list * term * term
     and thunk =
         SUS of term * thunk ref list
         | RES of value

fun splitAt (ls, n) = let
    fun splitAt' ([], _) = ([], [])
      | splitAt' (x :: xs, 1) = ([x], xs)
      | splitAt' (x :: xs, m) = let
          val (xs', xs'') = splitAt' (xs, m - 1)
      in (x :: xs', xs'') end
    in if n <= 0 then ([], ls) else splitAt' (ls, n) end

exception Impossible

fun papp (neu, args) = if length args > 0 then VAPP (neu, args) else VNEU neu

fun eval (defs, trm, env, args) =
    case trm of
        TAPP (func, arg) =>
        let val thunk = ref (SUS (arg, env))
        in eval (defs, func, env, thunk :: args) end
      | TLAM bod => (case args of
                        (arg :: args) => eval (defs, bod, arg :: env, args)
                      | [] => VLAM (bod, env))
      | TVAR idx => apply (defs, force (defs, List.nth (env, idx)), args)
      | TINT num => papp (NINT num, args)
      | TREF idx => eval (defs, Vector.sub (defs, idx), [], args)
      | TADD (idx1, idx2) =>
        let
            val value1 = force(defs, List.nth (env, idx1))
            val value2 = force(defs, List.nth (env, idx2))
        in
            (case (value1, value2) of
                 (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a+b), args)
               | _ => papp (NADD (value1, value2), args))
        end
      | TMUL (idx1, idx2) =>
        let
            val value1 = force(defs, List.nth (env, idx1))
            val value2 = force(defs, List.nth (env, idx2))
        in
            (case (value1, value2) of
                 (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a*b), args)
               | _ => papp (NMUL (value1, value2), args))
        end
      | TSUB (idx1, idx2) =>
        let
            val value1 = force(defs, List.nth (env, idx1))
            val value2 = force(defs, List.nth (env, idx2))
        in
            (case (value1, value2) of
                 (VNEU (NINT a), VNEU (NINT b)) => papp (NINT (a-b), args)
               | _ => papp (NSUB (value1, value2), args))
        end
      | TEQZ (idx, case1, case2) => 
        let
            val value = force(defs, List.nth (env, idx))
        in
            (case value of
                 VNEU (NINT a) =>
                 if a = 0
                 then eval (defs, case1, env, args) 
                 else eval (defs, case2, env, args) 
               | _ => papp (NEQZ (value, env, case1, case2), args))
        end
and apply (defs, value, args) =
    if length args = 0 then value else  
    case value of
        VAPP (neu, args') => VAPP (neu, args' @ args)
      | VNEU neu => VAPP (neu, args)
      | VLAM (trm, env) => eval (defs, trm, List.hd args :: env, List.tl args)
and force (defs, thunk) = case !thunk of
                        RES value => value
                      | SUS (trm, env) =>
                        let val res = eval (defs, trm, env, [])
                        in thunk := RES res; res end

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
(* val valT = TINT 5000000 *)
val valT = TINT 2000000
val listT = TAPP (TAPP (TREF 2, TREF 4), TINT 1)
(* val mainT = TAPP (TREF 3, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TAPP (TREF 7, TREF 5)))))))))) *)
val mainT = TAPP (TREF 3, TREF 5)

val defs = Vector.fromList [consT, nilT, repeatT, sumT, valT, listT, mainT, map1T, addT, subT]
val main = printVal (eval (defs, Vector.sub(defs, 6), [], []))
