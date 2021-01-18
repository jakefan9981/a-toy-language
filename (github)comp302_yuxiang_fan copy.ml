
(*  Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = match e with
  | Int n -> []
  | Bool b -> []
  | If(e1,e2,e3)->union (free_vars e1) (union (free_vars e2) (free_vars e3))
  | Primop(po,es)->List.fold_right (fun e1 fv -> union (free_vars e1) fv) es []
  | Tuple(es)->List.fold_right (fun e1 fv -> union (free_vars e1) fv) es []
  | Fn(y,t,e1)->delete [y] (free_vars e1)
  | Rec(y,t,e1)->delete [y] (free_vars e1)
  | Let(ds,e1)->(
      let rec findNames decls=match decls with
        |Val(e1,n)::xs|ByName(e1,n)::xs ->n::(findNames xs)
        |Valtuple(e1,nl)::xs->nl@(findNames xs)
        |[]-> []
      in
      let rec findFree decls acc=match decls with
        |Val(e1,n)::xs|ByName(e1,n)::xs->(
            let free=free_vars e1 in
            let cleanF=delete acc free in
            (cleanF)@(findFree xs (n::acc))
          )
        |Valtuple(e1,n)::xs ->
            let free=free_vars e1 in
            let cleanF=delete acc free in
            (cleanF)@(findFree xs (n@acc))
        |[]-> []
      in
      union (findFree ds []) (delete (findNames ds) (free_vars e1))
      (*union (delete (findNames ds) (findFree ds)) (delete (findNames ds) (free_vars e1))*)
      (*union (findFree ds ) (delete (findNames ds) (free_vars e1))*)
    )
  | Apply(e1,e2)-> union (free_vars e1) (free_vars e2)
  | Var y -> [y]
  | Anno(e1,t)->free_vars e1(*????*)



(*  Check variables are in use *)
let rec unused_vars (e : exp) : name list =
  let rec findNames decls=match decls with
    |Val(e1,n)::xs|ByName(e1,n)::xs ->n::(findNames xs)
    |Valtuple(e1,nl)::xs->nl@(findNames xs)
    |[]-> []
  in
  let rec findUnused decls=match decls with
    |Val(e1,n)::xs|ByName(e1,n)::xs->(unused_vars e1)@(findUnused xs)
    |Valtuple(e1,n)::xs -> (unused_vars e1)@(findUnused xs)
    |[]-> []
  in
  let rec cleanNs ns vs =
    let cleanNS= delete vs ns in
    let cleanVS= delete ns vs in
    union cleanNS cleanVS
  in
  let rec getAllN ex = match ex with
    |Let(ds,e1)-> (
        let allNames=cleanNs (findNames ds) (findUnused ds) in
        union allNames (getAllN e1)

      )
    |Fn(y,t,e1)->union [y] (getAllN e1)
    |Rec(y,t,e1)->union [y] (getAllN e1)
    |If(e1,e2,e3)->union (getAllN e1) (union (getAllN e2) (getAllN e3))
    |Primop(po,es)->List.fold_right (fun e1 fv -> union (getAllN e1) fv) es []
    |Var y->[y]
    |Int n->[]
    |Bool b->[]
    |Tuple (es) ->List.fold_right (fun e1 fv -> union (getAllN e1) fv) es []
    |Apply (e1,e2)->union (getAllN e1) (getAllN e2)
  in
  let rec getAllF ex2 = match ex2 with
    |Let(ds,e1)-> (
        getAllF e1
      )
    |Fn(y,t,e1)->getAllF e1
    |Rec(y,t,e1)->getAllF e1
    |If(e1,e2,e3)->union (getAllF e1) (union (getAllF e2) (getAllF e3))
    |Primop(po,es)->List.fold_right (fun e1 fv -> union (getAllF e1) fv) es []
    |Var y->[y]
    |Int n->[]
    |Bool b->[]
    |Tuple (es) ->List.fold_right (fun e1 fv -> union (getAllF e1) fv) es []
    |Apply (e1,e2)->union (getAllF e1) (getAllF e2)
  in
  delete (getAllF e) (getAllN e)


(*Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Let (ds, e2) -> (
      let rec replaceDS ds newN oldN=
        match ds with
        |Val(e1,n)::xs->(
            let newV=Var newN in
            if n=oldN then Val(e1,newN)::(replaceDS xs newN oldN)
            else Val(e1,n)::(replaceDS xs newN oldN)
          )
        |Valtuple(e1,nl)::xs->(
            let funct x =
              if x=oldN then newN
              else x
            in
            let nl'= List.map funct nl in
            Valtuple(e1,nl')::(replaceDS xs newN oldN)
          )
        |ByName(e1,n)::xs->(
            if n=oldN then Val(e1,newN)::(replaceDS xs newN oldN)
            else ByName(e1,n)::(replaceDS xs newN oldN)
          )
        |[]->[]
      in
      let rec nameList ds=match ds with
        |Val(e1,n)::xs->n::(nameList xs)
        |Valtuple(e1,nl)::xs->nl@(nameList xs)
        |ByName(e1,n)::xs->n::(nameList xs)
        |[]->[]
      in
      let member x l = List.exists (fun y -> y = x) l in

      let rec compareList unf f = match f with
        |x::xs->
            if member x unf then true
            else compareList unf xs
        |[]->false
      in
      let singleName sd = match sd with
        |Val(e4,n)->[n]
        |Valtuple(e4,nl)->nl
        |ByName(e4,n)->[n]
      in
      let parseSingle d unfreeV= match d with (*change here*)
        |Val (e1,n)->
            if  member n (free_vars e') && x=n then(
              let fList=(free_vars e1) in
              if compareList unfreeV fList then
                Val(e1,fresh_var n)
              else
                Val(subst (e',x) e1,fresh_var n)
            )
            else (
              let fList=(free_vars e1) in
              if compareList unfreeV fList then
                Val(e1, n)
              else
                Val(subst (e',x) e1,n)
            )
        |Valtuple(e1,nl)->
            let funct2 n =
              if member n (free_vars e') && x=n  then fresh_var n
              else n
            in
            let nl'= List.map funct2 nl in
            Valtuple(subst (e',x) e1,nl')
        |ByName(e1,n)->
            if member n (free_vars e') && x=n then ByName(subst (e',x) e1,fresh_var n)
            else ByName(subst (e',x) e1,n)
      in
      let rec parseDS ds unfreeV = match ds with
        |x::xs->(
            let singleUnfree=singleName x in
            (parseSingle x unfreeV)::(parseDS xs (singleUnfree@unfreeV))
          )
        |[]->[]
      in
      (*check all the names to see if x=y*)
      let namel = nameList ds in
      let freeE =(free_vars e') in
      let freeV =(free_vars e) in
      if (List.length freeV=0) then
        Let (ds, e2)
      else
        (if (member x namel) ||  (member x freeE) then
        (*rename *)
           let newN=(fresh_var x) in
           let e2'=subst (Var newN,x) e2 in
           let ds'=(replaceDS ds newN x) in
           Let (parseDS ds'[], subst (e',x) e2')
         else
           Let (parseDS ds [], subst(e',x)e2)
        )


    )
  | Fn (y, t, e1)->(
      if x = y then
         (* optimization: don't traverse e1 as there is not free occurrence of x in e2 *)
        Fn (y,t,e1)
      else
      if member y (free_vars e') then
        let y'  = fresh_var y in
        let e1' = subst (Var y',y) e1 in
        Fn(y',t,subst(e',x) e1')
      else
        Fn(y,t,subst(e',x)e1)
    )
  |Rec (y, t, e1)-> (
      Rec (y,t,subst(e',x)e1)

    )
  | Apply (e1, e2) -> Apply(subst(e',x)e1, subst(e',x)e2)


let eval_tests : (exp * exp) list = [

]

(* Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn (x, t, e)
      | Apply (e1, e2) -> (
          match eval e1 with
          |Fn(x,t,e3)->(
              let v = eval e2 in
              eval (subst (v,x) e3)
            )
          |_->stuck ("e1 should be a function in Apply e1 e2 ")
        )
      | Rec (f, t, e) -> (
          let f'= subst ((Rec (f, t, e)),f) e in
          eval f'
        )
      | Primop (And, es) ->(
          if (List.length es) = 2 then
            let (x::y::xs)=es in
            match (eval x) with
            |Bool true->eval y
            |Bool false->Bool false
            |_->stuck ("e1 must be a bool in && ")
          else stuck ("And is a binary operator. Number of args should be 2")

        )
      | Primop (Or, es) ->(
          if (List.length es) = 2 then
            let (x::y::xs)=es in
            match (eval x) with
            |Bool true->Bool true
            |Bool false->eval y
            |_->stuck ("e1 must be a bool in && ")
          else stuck ("And is a binary operator. Number of args should be 2")
        )
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Bad arguments to primitive operation"
            | Some v -> v
          end

      | Let (ds, e) -> (
          match ds with
          |[]->eval e
          |Val(e1,n)::xs->(
              let v = (eval e1) in
              let e5 = Let(xs,e) in
              eval (subst (v,n) e5)
            )
          |Valtuple(e1,nl)::xs->(
              let rec tupleEvaluate exp (nameL, valueL) = match (nameL, valueL) with
                |n::ns,v::vs->
                    (
                      let exp' = subst (v,n) exp in
                      tupleEvaluate exp' (ns,vs)
                    )
                |[],[]->exp
                |_,_->stuck "Tuple evaluation error"
              in
              match e1 with
              |Tuple el->(
                  let lengthV=(List.length el) in
                  let lengthN=List.length nl in
                  let v = (eval e1) in
                  if lengthV=lengthN then
                    let e5 = Let (xs ,e) in
                    eval (tupleEvaluate e5 (nl,el))
                  else
                    stuck "the lenght of name list must be equal to the length of value list in tuple"
                )
              |_->stuck "e must be a tuple if variable is a tuple"
            )
          |ByName(e1,n)::xs->(
              let e5 = Let(xs,e) in
              eval (subst (e1,n) e5)
            )
        )
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result


let infer_tests : ((context * exp) * typ) list = [
  (*
  *)
]

(* Type an expression *)
let rec infer (ctx : context) (e : exp) : typ =
  match e with
  |Int n->TInt
  |Bool b->TBool
  |Var n->ctx_lookup ctx n
  |If (e1,e2,e3)->(
      match infer ctx e1 with
      |TBool->
          if typ_eq (infer ctx e2)  (infer ctx e3) then
            (infer ctx e2)
          else raise (TypeError "e2 and e3 should have the same type")
      |_->raise (TypeError "e1 in an if statement should be of type bool")

    )
  |Primop (op,el)->(
      let el' = List.map (infer ctx) el in
      if (List.length el' = 2) || (List.length el' = 1) then
        match el' with
        |(TInt)::(TInt)::xs->
            (
              match op with
              |Plus|Minus|Times|Div->TInt
              |Equals|NotEquals|LessThan|LessEqual|GreaterThan|GreaterEqual->TBool
              |_ ->raise (TypeError "this op cannot be applied to two ints")
            )
        |(TBool)::(TBool)::xs->
            (
              match op with
              |Or|And->TBool
              |_ ->raise (TypeError "this op cannot be applied to two bools")
            )
        |(TInt)::[]->
            (
              match op with
              |Negate->TInt
              |_->raise (TypeError "the op in op e1 should be Negate")
            )
        |_ -> raise (TypeError "arguments in op should be int or bool")
      else raise (TypeError " op should have one or two expressions" )
    )
  |Tuple(es)->TProduct (List.map (infer ctx) es)
  |Fn(y,Some(t),e1)->(
      let result=infer (extend ctx (y,t)) e1 in
      TArrow (t,result)
    )
  |Rec(y,t,e1)->infer (extend ctx (y,t)) e1
  |Anno(e1,t)->infer ctx e1
  |Let (ds,e1)->(
      match ds with
      |Val(e2,n2)::xs-> (
          let typ=infer ctx e2 in
          infer (extend ctx (n2,typ)) (Let (xs, e1))
        )
      |Valtuple(e2,nl)::xs->(

          let rec tupleList (nameL, typeL) = (
            match (nameL, typeL) with
            |name::ns,ty::ts->(name,ty)::tupleList(ns,ts)
            |[],[]->[]
            |_ ->raise (TypeError "name list and e in Valtuple must have the same length")
          )
          in
          let typs=infer ctx e2 in
          match typs with
          |TProduct(tl)->(
              if (List.length tl) = (List.length nl) then
                let tupleL= tupleList (nl,tl) in
                infer (extend_list ctx tupleL) (Let (xs,e1))
              else raise (TypeError "name list and e in Valtuple must have the same length")
            )
          |_ ->raise (TypeError "e in Valtuple must be a list")

        )
      |ByName(e2,n2)::xs->(
          let typ=infer ctx e2 in
          infer (extend ctx (n2,typ)) (Let (xs,e1))

        )
      |[]->infer ctx e1
    )
  |Apply(e1,e2)->(
      let f=infer ctx e1 in
      match f with
      |TArrow(t1,t2)->
          if typ_eq (infer ctx e2) t1 then t2
          else raise (TypeError "e2 must have a type x in function x->x2")
      |_ -> raise (TypeError "e1 in apply must be a function")

    )
  |Fn(y,None,e2)->raise (TypeError "functions in question 5 should be annoted with its type" )



let unify_tests : ((typ * typ) * unit) list = [
  (*
      v2 = fresh_tvar()
     TVar (ref (Some (TArrow (v2,v2))))
     *)
]


(* Unify two types *)
let rec unify (ty1 : typ) (ty2 : typ) : unit = (
  let rec findAllAlpha type1= match type1 with
    |TInt-> []
    |TBool->[]
    |TVar(r)->([r] )
    |TArrow(t1,t2)->(findAllAlpha t1)@(findAllAlpha t2)
    |TProduct(tl)->List.flatten (List.map (findAllAlpha) tl)
  in
  let rec isThere r rl = match rl with
    |singleR::rs->
        if r==singleR then true
        else isThere r rs
    |[]->false
  in
  match ty1 with
  |TInt->(
      match ty2 with
      |TInt->()
      |TVar(x)->(
          match !x with
          |Some(TInt)->()
          |Some(TBool)-> raise (TypeError "int cannot be unified with bool")
          |Some(TProduct(tl))->raise (TypeError "int cannot be unified with a product type")
          |Some (TArrow(t1,t2))->raise (TypeError "int cannot be unified with a arrow type")
          |None->x := Some(TInt)
          |_ ->raise (TypeError "int cannot be unified with this type")
        )
      |_ -> raise (TypeError "ty2 cannot be unified with TInt")
    )
  |TBool->(
      match ty2 with
      |TBool->()
      |TVar(x)->(
          match !x with
          |Some(TInt)->raise (TypeError "bool cannot be unified with int")
          |Some(TBool)-> ()
          |Some(TProduct(tl))->raise (TypeError "bool cannot be unified with a product type")
          |Some (TArrow(t1,t2))->raise (TypeError "bool cannot be unified with a arrow type")
          |None->x := Some(TBool)
          |_ ->raise (TypeError "bool cannot be unified with this type")
        )
      |_ ->raise (TypeError "this cannot be unified with TBool")
    )
  |TVar(x)->(
      match !x with
      |None->(
          match ty2 with
          |TInt-> x := Some (TInt)
          |TBool-> x := Some(TBool)
          |TVar(x2)-> (
              let rl= (findAllAlpha ty2) in
              if isThere x rl then
                if (List.length rl =1) then x := (!x2)
                else raise (TypeError "ty1 is a type variable that belongs to FV(ty2), a Tvar")
              else
                x := !x2;
            )
          |TArrow(t1,t2)->(
              let rl = (findAllAlpha ty2) in
              if isThere x rl then raise (TypeError "ty1 is a type variable that belongs to FV(ty2), a Arrow")
              else
                x := Some(ty2)
            )
          |TProduct (tpl)->(
              let rl = (findAllAlpha ty2) in
              if isThere x rl then raise (TypeError "ty1 is a type variable that belongs to FV(ty2),a tuple")
              else   x := Some(ty2)
            )
        )
      |Some(t3)-> (
          match ty2 with
          |TInt->
              if t3=TInt then ()
              else raise (TypeError "Tvar is not type int so it cannot be unified with int")
          |TBool->
              if t3=TBool then ()
              else raise (TypeError "Tvar is not type bool so it cannot be unified with bool")
          |TVar(x2)-> (
              match (!x2) with
              |None->raise (TypeError "those two Tvars have different contents")
              |Some(v)->(
                  if v = t3 then ()
                  else (
                    raise (TypeError "those two Tvars have different contents")
                  )
                )
            )
          |TArrow(t1,t2)->(
              if t3=ty2 then (
                unify ty2 t3
              )
              else raise (TypeError "Tvar is not type arrow so it cannot be unified with type arrow")
            )
          |TProduct (tpl)->(
              if t3=ty2 then (
                unify ty2 t3
              )
              else raise (TypeError "Tvar is not type tuple so it cannot be unified with type tuple")
            )
        )
    )
  |TArrow(t1,t2)->(
      match ty2 with
      |TInt->raise (TypeError "Tarrow cannot unified with Tint")
      |TBool->raise (TypeError "Tarrow cannot unified with TBool")
      |TProduct(tpl2)->raise (TypeError "Tarrow cannot unified with TProduct")
      |TVar(x3)-> (
          match !x3 with
          |Some(TArrow(t4,t5))->(
              if (t1==t4 && t2==t5) then ()
              else
                (
                  unify t1 t4;
                  unify t2 t5
                )

            )
          |None->(
              let rl = (findAllAlpha ty1) in
              if isThere x3 rl then raise (TypeError "ty2 is a type variable that belongs to FV(ty1), a Arrow")
              else
                x3 := Some(ty1)
            )
          |_-> raise (TypeError "Tarrow cannot unified with TVar when TVar is not Tarrow")
        )
      |TArrow(t4,t5)->(
          if (t1==t4 && t2==t5) then ()
          else
            (
              unify t1 t4;
              unify t2 t5
            )

        )
    )
  |TProduct (tl)->(
      match ty2 with
      |TProduct(tl2)->(
          if (List.length tl)=(List.length tl2) then (
            let result = List.map2 (fun type1-> fun type2-> unify type1 type2) tl tl2 in
            ()
          )
          else raise (TypeError "Error:Two Tproducts have different length")
        )
      |TVar(x4)->(
          match !x4 with
          |Some(TProduct(tl2))->(
              if (List.length tl)=(List.length tl2) then (
                let result = List.map2 (fun type1-> fun type2-> unify type1 type2) tl tl2 in
                ()
              )
              else raise (TypeError "Error:Two Tproducts have different length")

            )
          |_ ->raise (TypeError "Tproduct cannot be unified with ty2")
        )
      |_ ->raise (TypeError "Tproduct cannot be unified with ty2")
    )
)
