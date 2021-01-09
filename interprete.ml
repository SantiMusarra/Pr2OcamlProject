type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
           Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
           Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
           Letrec of ide * exp * exp
(*Estensione exp*)
  | Estring of string
  | EmptySet of exp
  | Singleton of exp * exp
  | Insert of exp * exp
  | Delete of exp * exp
  | IsEmpty of exp
  | Member of exp * exp
  | SubSet of exp * exp
  | FindMin of exp
  | FindMax of exp
  | Merge of exp * exp
  | Intersection of exp * exp
  | Difference of exp * exp
  | ForAll of exp * exp
  | Exists of exp * exp
  | Filter of exp * exp
  | Map of exp * exp
;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun 
(*Estensione dei tipi esprimibili*)
  | StringVal of string
  | SetElements of (evT list) * ide
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let rec typecheck (s : string) (v : evT) : bool = match s with
    "int" -> (match v with
        Int(_) -> true
      | _ -> false)
  | "bool" -> (match v with
        Bool(_) -> true
      | _ -> false)
(*Estensione typecheck*)
  | "string" -> (match v with
        StringVal(_) -> true
      | _ -> false
    )
  | _ -> failwith("not a valid type")
;;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n*u)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n+u)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Int(n-u)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        (Int(n),Int(u)) -> Bool(n=u)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let minus x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Int(-n)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
        Int(n) -> Bool(n=0)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> (Bool(b||e))
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        (Bool(b),Bool(e)) -> Bool(b&&e)
      | _-> failwith ("Type error"))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
        Bool(true)  -> Bool(false)
      | Bool(false) -> Bool(true)
      | _-> failwith ("Type error"))
  else failwith("Type error");;
;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, lBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval lBody r1 |
            		_ -> failwith("non functional def"))

(* Estensione interprete*)
  (* Stringa *)
  | Estring(a) -> StringVal a

  (* Crea un Set vuoto *)
  | EmptySet(tipo) -> 
    (match eval tipo r with 
      StringVal(s) -> SetElements([],s)
      | _ -> failwith("Type error"))

  (* Crea un Set con un elemento controllando che i tipi siano uguali *)
  | Singleton(element,tipo) -> let evalEl = eval element r in
      (match eval tipo r with 
      StringVal(s) -> if (typecheck s evalEl) then SetElements([evalEl],s) else failwith("Element's type is not equal to Set's type")
      | _ -> failwith("Type error"))
  
  (* Inserisce nel Set un elemento con la funzione ausiliaria insertFunction *)
  | Insert(set,element) -> 
      let evalEl = eval element r in
      (match eval set r with
         SetElements(lst,t) -> if (typecheck t evalEl) then 
                                  if(contains lst evalEl) then failwith("Element already exist")
                                  else SetElements( evalEl::lst,t )
           else failwith("Element's type is not equal to Set's type")
       | _ -> 	failwith("Type error: not a Set")
      )

  (* Rimuove dal Set un elemento con la funzione ausiliaria deleteFromSet *)
  | Delete(set,element) -> 
      let evalEl = eval element r in
      (match eval set r with
         SetElements(lst,t) -> if (typecheck t evalEl) then SetElements(deleteFromSet lst evalEl,t)
           else failwith("Element's type is not equal to Set's type")
       | _ -> 	failwith("Type error: not a Set")
      )

  (* Controlla se un Set è vuoto *)
  | IsEmpty(set) -> 
      (match eval set r with
         SetElements([],t) -> Bool true
        | SetElements(lst,t) -> Bool false 
        | _ -> failwith("Type error")
      )

  (* Controlla se l'elemento è presente nel Set con la funzione ausiliaria contains *)
  | Member(set,element) -> 
      let evalEl = eval element r in
      (match eval set r with
         SetElements(lst,t) -> Bool(contains lst evalEl)
       | _-> failwith("Type error")
      )

  (* Controlla se un Set è sottoinsieme dell altro con la funzione ausiliaria isSubSet *)
  | SubSet(set1, set2) -> let evalList1 = eval set1 r in
      let evalList2 = eval set2 r in
      (match evalList1, evalList2 with
         SetElements(lst1, t1), SetElements(lst2, t2) -> if t1 = t2 then Bool(isSubSet lst1 lst2) else Bool false
       | _-> failwith("Type error"))

  (* Cerca il valore più piccolo in un Set*)
  | FindMin (set) -> 
      (match eval set r with
         SetElements([],t) -> failwith ("Empty Set")
        | SetElements(lst,t) -> getMin lst
        | _-> failwith("Type error"))

  (* Cerca il valore più grande in un Set *)
  | FindMax (set) -> 
      (match eval set r with
        SetElements([],t) -> failwith ("Empty Set")
        | SetElements(lst,t) -> getMax lst
        | _-> failwith("Type error"))

  (* Unisce due Set solo se sono dello stesso tipo *)
  | Merge(set1, set2) -> let evalSet1 = eval set1 r in
      let evalSet2 = eval set2 r in
      (match evalSet1, evalSet2 with
         SetElements(lst1, t1), SetElements(lst2, t2) -> if t1 = t2 then SetElements(lst1@lst2, t1)
           else failwith ("Sets type not equal")
       | _-> failwith("Type error"))

  (* Interseca due Set utilizzando la funzione ausiliaria intersection *)
  | Intersection(set1, set2) -> let evalSet1 = eval set1 r in
      let evalSet2 = eval set2 r in
      (match evalSet1, evalSet2 with
         SetElements(lst1, t1), SetElements(lst2, t2) -> if t1 = t2 then SetElements((intersection lst1 lst2 []), t1)
           else failwith ("Sets type not equal")
       | _-> failwith("Type error"))

  (* Ritorna la differenza tra due Set utilizzando la funzione ausiliaria difference *)
  | Difference(set1, set2) -> let evalSet1 = eval set1 r in
      let evalSet2 = eval set2 r in
      (match evalSet1, evalSet2 with
         SetElements(lst1, t1), SetElements(lst2, t2) -> if t1 = t2 then SetElements((difference lst1 lst2 []), t1)
           else failwith ("Sets type not equal")
       | _-> failwith("Type error"))

  (* Controlla che tutti gli elementi del Set rispettino il predicato dato utilizzando la funzione ausiliaria forall *)
  | ForAll(predicate , set) -> 
      (match eval set r with
         SetElements(lst, t) -> Bool(forall lst predicate r)
       | _ -> failwith("Type error"))

  (* Controlla che esista almeno un elemento del Set che soddisfi il predicato utilizzando la funzione ausiliaria exists *)
  | Exists(predicate, set) ->	
      (match eval set r with
         SetElements(lst,t) -> Bool(exists lst predicate r)
       | _ -> failwith("Type Error"))

  (*Restituisce un Set con tutti gli elementi che rispettano il predicato ed utilizza la funzione ausiliaria filter *)
  | Filter(predicate, set) ->	
      (match eval set r with
         SetElements(lst,t) -> SetElements(filter lst [] predicate r,t)
       | _ -> failwith("Type Error"))

  (* Ad ogni elemento del Set viene applicata la funzione f con la funzione ausiliaria map *)
  | Map(f ,set) -> 
      (match  eval set r with
         SetElements(lst,t) -> SetElements(map lst [] f r,t)
       | _ -> failwith("Type Error"))

(*Funzioni Ausiliarie *)

and fromEvtToExp (t:evT) : exp = match t with
    Bool b -> Ebool b
  | StringVal d -> Estring d
  | Int i -> Eint i
  | _ -> failwith("Type error")

and contains (lst: evT list)	(el: evT): bool =	
  (match lst with
      []-> false
    | x::xs -> if x = el then true else contains xs el
  )

and deleteFromSet (lst: evT list) (el: evT) : evT list = (match lst with
      [] -> []
    | x::xs-> if x= el then xs else x :: deleteFromSet xs el
  )

and isSubSet (lst1: evT list) (lst2: evT list) : bool = (match lst1, lst2 with
      [], lst2 -> true
    | x :: xs, lst2 -> if contains lst2 x  then isSubSet xs lst2 else  false )

and getMin (lst: evT list) : evT = (match lst with
      [] -> failwith ("Input error")
    | [x] -> x
    | x :: xs -> if x < getMin xs then x else getMin xs )

and getMax (lst: evT list) : evT = (match lst with
      [] -> failwith ("Input error")
    | [x] -> x
    | x :: xs -> if x > getMax xs then x else getMax xs )

and intersection (lst1: evT list) (lst2: evT list) (lst: evT list): evT list = (match lst1 with
      [] -> lst
    | x:: xs -> if contains lst2 x then intersection xs lst2 (x :: lst) else intersection xs lst2 lst)

and difference (lst1: evT list) (lst2: evT list) (lst: evT list): evT list = (match lst1 with
      [] -> lst
    | x:: xs -> if (contains lst2 x)  then difference xs lst2 lst else difference xs lst2 (x :: lst))

and forall (lst: evT list) (p: exp) (env1: evT env): bool = (match lst with
      [] -> false
    | x::xs -> (match eval (FunCall(p, fromEvtToExp x)) env1 with
          Bool true -> forall xs p env1
        | Bool false -> false
        | _ -> failwith("Invalid result")
      )
  )
and exists (lst: evT list) (p: exp) (env1: evT env): bool = (match lst with
      [] -> false
    | x::xs -> (match eval (FunCall(p,fromEvtToExp x)) env1 with
          Bool true -> true
        | Bool false -> forall xs p env1
        | _ -> failwith("Invalid result")
      )
  )
and filter (lst: evT list) (l: evT list) (p: exp) (env1: evT env): evT list= (match lst with
      [] -> l
    | x::xs -> (match eval (FunCall(p,fromEvtToExp x)) env1 with
          Bool true -> filter xs (x::l) p env1
        | Bool false -> filter xs l p env1
        | _ -> failwith("Invalid result")
      )
  )
and map (lst: evT list) (l: evT list) (p: exp) (env1: evT env): evT list= (match lst with
      [] -> l
    | x::xs ->  (let a = FunCall(p,fromEvtToExp x) in 
                  let evalA = (eval a env1) in 
                    map xs (evalA::l) p env1)
  )

;;

(* --------------  TEST --------------*)

(* creazione di un ambiente vuoto *)
let env0 = emptyenv Unbound;;

(* Creazione di insiemi con integer o stringhe*)
let intSet = EmptySet(Estring("int"));;
eval intSet env0;;

let intSet2 = EmptySet(Estring("int"));;
eval intSet2 env0;;

let stringSet = EmptySet(Estring("string"));;
eval stringSet env0;;

let singletonSet = Singleton(Estring ("Hello world"),Estring ("string"));;
eval singletonSet env0;;


(* Test Inserimento e Rimozione *)
let intSet = Insert(Insert(Insert(intSet, Eint(13)), Eint(6)), Eint(2));;
let intSet = Delete(intSet,Eint(13));;
eval intSet env0;;

let intSet2 = Insert(Insert(Insert(intSet2, Eint(15)), Eint(5)), Eint(10));;
let intSet2 = Delete(intSet2,Eint(10));;
eval intSet2 env0;;

let stringSet = Insert(Insert(Insert(stringSet,Estring("c")),Estring("b")),Estring("a"));;
let stringSet = Delete(stringSet,Estring("c"));;
eval stringSet env0;;


(* test delle operazioni di intersezione, unione e differenza *)

let testMerging = Merge(intSet, intSet2);;
eval testMerging env0;; (* unione tra intSet e intSet2*)

let testIntr = Intersection(intSet, intSet2);;
eval testIntr env0;;  (* intersezione tra intSet e intSet2*)

let testDiff = Difference(intSet, intSet2);;
eval testDiff env0;;  (* differenza tra intSet e intSet2*)

(* Test delle operazioni di base *)

let testEmpty = IsEmpty(intSet);;
eval testEmpty env0;; (* Se corretto ritorna: Bool false *)

let testMember = Member(stringSet, Estring("a"));;
eval testMember env0;; (* Se corretto ritorna: Bool true *)

let testSub = SubSet(stringSet, intSet);;
eval testSub env0;; (* Se corretto ritorna: Bool false *)

let trovaMin = FindMin(intSet);;
eval trovaMin env0;; (* Se corretto ritorna: 2 *)

let trovaMax = FindMax(intSet);;
eval trovaMax env0;; (* Se corretto ritorna: 13 *)

(*Test delle altre operazioni effettuate sull'insieme intSet*)

let func1 = Fun("x", Ifthenelse(IsZero(Den "x"), Ebool true, Ebool false));; (* Verifica se sono presenti numeri uguale a 0 *)
let func2 = Fun("x", Prod(Den "x", Den "x"));; (* Raddoppia il numero *)

let forall = ForAll(func1,intSet);;
eval forall env0;; (* Se corretto ritorna: Bool false *)

let exists = Exists(func1,intSet);;
eval exists env0;; (* Se corretto ritorna: Bool false *)

let filter = Filter(func1,intSet);;
eval filter env0;; (* Se corretto ritorna: []*)

let map = Map(func2,intSet);;
eval map env0;; (* Se corretto ritorna: elementi raddoppiati*)