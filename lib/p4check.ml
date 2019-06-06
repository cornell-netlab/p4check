(* Copyright 2019-present Cornell University
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy
 * of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *)

open Petr4
open Types
open Core

(* Header Types *)
module HSet =
  Set.Make(struct
      type t = string [@@deriving compare, sexp, hash]
    end)

(* Environments *)
module HMap =
  Map.Make(struct
      type t = string [@@deriving compare, sexp]
    end)

let format_list (fmt_el:Format.formatter -> int -> unit) (sep:string)  (fmt:Format.formatter) (l:int list) =
  let use_separator = ref false in
  List.iter l ~f:(fun x ->
      (if !use_separator then
        Format.fprintf fmt "%s" sep);
      fmt_el fmt x;
      use_separator := true;
    )

  
module Type : sig 
  type t 
  val empty : t
  val epsilon : t
  val header : string -> t
  val concat : t -> t -> t
  val union : t -> t -> t
  val restrict : t -> string -> t
  val neg_restrict : t -> string -> t
  val add : t -> string -> t
  val remove : t -> string -> t
  (* val copy : t -> string -> string -> t *)
  val valid : t -> string -> bool
  val contradiction: t -> bool
  val format : Format.formatter -> t -> unit
  val size : t -> int
end = struct
  module S = struct
    type t = string [@@deriving hash,sexp,compare] 
  end
  module I = struct
    type t = int [@@deriving hash,sexp,compare] 
  end
  module II = struct
    type t = int * int [@@deriving hash,sexp,compare] 
  end
  module III = struct
    type t = int * int * int [@@deriving hash,sexp,compare] 
  end
  module IL = struct
    type t = int * (int * int) list [@@deriving hash,sexp,compare] 
  end
  module H = Hashcons.Make(S)
  module C = struct
    include Set.Make(I)
    include Provide_hash(I)
  end
  module U = C
  module CH = Hashcons.Make(C)
  module UH = Hashcons.Make(U)
  module HT = Hashtbl.Make(I)
  module HTT = Hashtbl.Make(II)
  module HTTT = Hashtbl.Make(III)
  module HTL = Hashtbl.Make(IL)

  type t = int

  let rec format fmt t =
    let fmt_h fmt x = Format.fprintf fmt "%s" (H.unget x) in 
    let fmt_c fmt c = 
      match C.elements (CH.unget c) with 
      | [x] -> fmt_h fmt x
      | l -> Format.fprintf fmt "(%a)" (format_list fmt_h " . ") l in
    Format.fprintf fmt "{%a}" (format_list fmt_c " + ") (U.elements (UH.unget t))

  (* Constructors *)
  let real_empty = U.empty
  let empty = real_empty |> UH.get

  let real_epsilon = U.singleton (CH.get (C.empty))
  let epsilon = real_epsilon |> UH.get

  let header h = UH.get (U.singleton (CH.get (C.singleton (H.get h))))

  let real_concat t1 t2 =
    U.fold t1 ~init:U.empty ~f:(fun acc c1 ->
        U.fold t2 ~init:acc ~f:(fun acc c2 -> 
            U.add acc (CH.get (C.union (CH.unget c1) (CH.unget c2)))))

  let concat = 
    let memo = HTT.create () in 
    fun t1 t2 ->
      match HTT.find memo (t1,t2) with
      | None -> 
        let r = real_concat (UH.unget t1) (UH.unget t2) |> UH.get in 
        HTT.add_exn memo ~key:(t1,t2) ~data:r;
        r
      | Some r -> 
        r

  let real_union t1 t2 = U.union t1 t2

  let union = 
    let memo = HTT.create () in 
    fun t1 t2 ->
      match HTT.find memo (t1,t2) with
      | None -> 
        let r = real_union (UH.unget t1) (UH.unget t2) |> UH.get in 
        HTT.add_exn memo ~key:(t1,t2) ~data:r;
        r
      | Some r -> 
        r

  (* Operations *)
  let rec restrict = 
    let memo = HTT.create() in 
    fun t h ->
      let n = H.get h in
      match HTT.find memo (t,n) with
      | None -> 
        let r = 
          U.fold (UH.unget t) ~init:U.empty ~f:(fun u c -> if C.mem (CH.unget c) n then U.add u c else u) |>
          UH.get in 
        HTT.add_exn memo ~key:(t,n) ~data:r;
        r
      | Some r -> 
        r

  let rec neg_restrict = 
    let memo = HTT.create() in 
    fun t h ->
      let n = H.get h in
      match HTT.find memo (t,n) with
      | None -> 
        let r = 
          U.fold (UH.unget t) ~init:U.empty ~f:(fun u c -> if not (C.mem (CH.unget c) n) then U.add u c else u) |>
          UH.get in 
        HTT.add_exn memo ~key:(t,n) ~data:r;
        r
      | Some r -> 
        r

  let add = 
    let memo = HTT.create () in 
    fun t h ->
       let n = H.get h in 
       match HTT.find memo (t,n) with 
       | None -> 
         let r = 
           U.fold (UH.unget t) ~init:U.empty
             ~f:(fun us c -> 
                 let cs = CH.unget c in
                 let cs' = C.add cs n in
                 U.add us (CH.get cs')) |>
           UH.get in 
         HTT.add_exn memo ~key:(t,n) ~data:r;
         r
       | Some r -> 
         r
    
  let rec remove = 
    let memo = HTT.create () in 
    fun t h ->
       let n = H.get h in 
       match HTT.find memo (t,n) with 
       | None -> 
         let r = 
           U.fold (UH.unget t) ~init:U.empty
             ~f:(fun us c -> 
                 let cs = CH.unget c in
                 let cs' = C.filter cs ~f:((<>) n) in 
                 U.add us (CH.get cs')) |>
           UH.get in 
         HTT.add_exn memo ~key:(t,n) ~data:r;
         r
       | Some r -> 
         r

  let rec copy = 
    let memo = HTTT.create () in 
    fun t h1 h2 ->
       let n1 = H.get h1 in 
       let n2 = H.get h2 in 
       match HTTT.find memo (t,n1,n2) with 
       | None -> 
         let r = 
           U.fold (UH.unget t) ~init:U.empty
             ~f:(fun us c -> 
                 let cs = CH.unget c in
                 let cs' = if C.mem cs n2 then C.add cs n1 else C.remove cs n1 in
                 U.add us (CH.get cs')) |>
           UH.get in 
         HTTT.add_exn memo ~key:(t,n1,n2) ~data:r;
         r
       | Some r -> 
         r

  let contradiction t = U.is_empty (UH.unget t)
      
  let valid = 
    let memo = HTT.create() in 
    fun t h ->
      let n = H.get h in
      match HTT.find memo (t,n) with
      | None -> 
        let u = UH.unget t in 
        let r = not (U.is_empty u) && U.for_all u ~f:(fun c -> C.mem (CH.unget c) n) in 
        HTT.add_exn memo ~key:(t,n) ~data:r;
        r
      | Some r -> 
        r
  let size t = UH.unget t |> U.length
end


let name_of_inst name idx_option = 
  let str =  snd name in
  match idx_option with 
  | None -> str
  | Some n -> Printf.sprintf "%s[%d]" str n

let int_of_expr (expr : Expression.t) : int =
  match expr with
  | (_, Expression.Int (_, i)) -> i.value |> Bigint.to_int_exn
  | _ -> failwith "expecting constant, got expression"

            
let all_insts (p : program) (header_struct_name : string) =
  let open TopDeclaration in
  let Program(decls) = p in
  
  let f acc (info, field) =
    let open TypeDeclaration in
    match field.typ with
    | (_, HeaderStack hs ) ->
       begin
         match hs.size with
         | (_, Int size) ->
            let rec loop j acc =
              if Bigint.of_int j = (snd size).value then
                acc
              else
                HSet.add acc (name_of_inst field.name (Some j))
                |> loop (j+1)
            in
            loop 0 acc
         | _ -> failwith "cannot process header stack initialized with expression"
       end
    | _ -> HSet.add acc (name_of_inst field.name None)       
  in
  List.fold_left decls ~init:None
    ~f:(fun acc decl ->
      match acc with
      | Some x -> acc
      | None ->
         match decl with
         | TypeDeclaration (_, Struct{annotations; name; fields}) ->
            if snd name = header_struct_name then
              Some (List.fold_left fields ~init:HSet.empty ~f:f)
            else
              None
         | _ -> None
    ) |> Option.value ~default:HSet.empty
  

let lookup_parser_state prog pname statename =
  (* Printf.printf "Looking for parser %s\n" pname; *)
  let Program decls = prog in
  List.fold decls ~init:None
    ~f:(fun state decl ->
      match state with
      | Some _ -> state
      | None ->
         begin
           let open Declaration in
           match decl with
           | TypeDeclaration _ -> state
           | Declaration decl ->
              match decl with
              | ((_, Parser p) as prsr) ->
                 (* Printf.printf "Found parser %s\n" (snd (name prsr)); *)
                 if snd p.name = pname then
                   (* let () = Printf.printf "looking for \"%s\" state\n" statename in *)
                   List.fold p.states ~init:None
                     ~f:(fun res ((_,s) as state) ->
                       (* let () = Printf.printf "\tLooking at state %s\n" (snd s.name) in *)
                       match res with
                       | None ->
                          if statename = snd s.name then
                            (* let ()  = Printf.printf "\t which matches\n" in *)
                            Some(prsr, state)
                          else
                            res
                       | Some x -> (* let () = Printf.printf "\tbut I already found %s\n" statename in *)
                                   res
                     )
                 else state
              | (_,_) -> None
         end
    )

let lookup_action_function (prog : program) (decl : Declaration.t) (string:string) : Declaration.t option  =
  let open Declaration in
  (* Printf.printf "\nCALLED LOOKUP_ACTION_FUNCTION\n";
   * Printf.printf "[lookup_action_function] Looking for %s in %s\n" (string) (snd (name decl)); *)
  match snd decl with
  | Control c ->
     begin
       (* Printf.printf "[lookup_action_function] checking %d local declarations\n" (List.length c.locals); *)
       let local_lookup = List.fold c.locals ~init:None
                            ~f:(fun func_opt decl' ->
                              (* Printf.printf "[lookup_action_function] checking %s\n" (snd (name decl')); *)
                              match func_opt, decl' with
                              | Some _, _ -> func_opt
                              | None, ((_,Action a) as ainf) ->
                                 (* Printf.printf "~~ Checking whether %s = %s ~~ \n" (snd a.name) (string); *)
                                 if snd a.name = string then
                                   (* let () = Printf.printf "\tit does \n" in *)
                                   Some ainf
                                 else
                                   (* let () = Printf.printf "\tit does not\n" in *)
                                   func_opt
                              | _, _ -> func_opt)
       in
       match local_lookup, prog with
       | Some f, _ -> Some f
       | None, Program(decls) ->
          List.fold decls ~init:None ~f:(fun func_opt decl' ->
              match func_opt, decl' with
              | Some _, _ -> func_opt
              | None, (Declaration((_,Action a) as ainf)) ->
                 if snd a.name = string then
                   Some ainf
                 else
                   None
              | _, _ -> func_opt
            )
     end
  | _ -> None
                                       

let lookup_control_state prog cname : Declaration.t option =
  let Program decls = prog in
  (* Printf.printf "finding %s in %d decls\n" cname (List.length decls); *)
  List.fold decls ~init:None
    ~f:(fun state decl ->
      match state with
      | Some _ -> state
      | None ->
         begin
           let open Declaration in
           match decl with
           | TypeDeclaration _ -> state
           | Declaration decl ->
              match decl with
              | (_, Control c ) ->
                 if cname = snd c.name then
                   (* let () = Printf.printf "%s = %s\n" cname (snd c.name) in *)
                   Some decl
                 else
                   (* let () = Printf.printf "%s <> %s\n" cname (snd c.name) in *)
                   state
              | _ -> None
         end      
    )  

let lookup_ctrl_inst_decl_list prog decl_list iname =
  let open TopDeclaration in
  let open Declaration in
  List.fold decl_list ~init:None
    ~f:(fun state decl ->
      match state with
      | Some _ -> state
      | None ->
         begin
           match decl with
           | TypeDeclaration _ -> state
           | Declaration decl ->
              if snd (name decl) = iname then
                let error_msg seen_type =
                  failwith ("Error :: expecting control instance, got "
                            ^ seen_type ^ ": [" ^ snd (name decl)
                            ^ "] at " ^ Petr4.Info.to_string (fst (name decl)))
                in
                match decl with
                | (info, Instantiation c ) ->
                   if iname = snd c.name then
                     let open Type in
                     match c.typ with
                     | _, (TypeName tn) ->
                        lookup_control_state prog (snd tn)
                     | _ -> failwith ( "ERROR :: Don't know how to lookup instantiation type that isn't a name at "
                                       ^ Petr4.Info.to_string info)
                   else
                     state
                | (_, Constant _) -> error_msg "Constant"
                | (_, Parser _) -> error_msg "Parser Declaration"
                | (_, Control _) -> error_msg "Control Declaration"
                | (_, Function _) -> error_msg "Function"
                | (_, ExternFunction _ ) -> error_msg "ExternFunction"
                | (_, Variable _) -> error_msg "Variable"
                | (_, ValueSet _) -> error_msg "ValueSet"
                | (_, Action _) -> error_msg "Action"
                | (_, Table _) -> error_msg "Table"
              else
                None
         end)
    
  
let lookup_control_instance prog ctx iname : Declaration.t option =
  let open TopDeclaration in
  let open Declaration in
  let Program decls = prog in
  match snd ctx with
  | Control c ->
     begin
       let local_lookup = lookup_ctrl_inst_decl_list prog (List.map ~f:(fun x -> Declaration x) c.locals) iname  in
       match local_lookup with
       | Some d -> Some d
       | None ->
          let global_lookup = lookup_ctrl_inst_decl_list prog decls iname in
          match global_lookup with
          | Some d -> Some d
          | None ->
             (* maybe iname is really a direct application, try that *)
             lookup_control_state prog iname
     end
  | _ -> failwith "Error :: Expecting control got other type"
  
                   

let rec acc_members ?name:(name=true) ?stack_idx:(stack_idx=None) exp_mem : string option * bool =
  let open Expression in
  match exp_mem with
  | ExpressionMember {expr=(_,exp_mem'); name=name'} ->
     let open Option in
     if snd name' = "last" then
       match acc_members ~name exp_mem' with
       | None, b -> None, b
       | Some acc_name, b ->
          match stack_idx with
          | None -> Some (acc_name) , true
          | Some idx -> Some (acc_name ^ "[" ^ Int.to_string idx ^ "]") , b
     else
       begin
         match acc_members ~name exp_mem' with
         | None, b -> None, b
         | Some acc_name, b ->
            if String.length acc_name = 0 then
              Some (snd name'), b
            else 
              Some (acc_name ^ "." ^ snd name'), b
       end
  | Name (_,n) ->
     (* Printf.printf "[acc_members] base name is %s" n; *)
     if name then
       (* let () = Printf.printf " keeping it\n" in *)
       Some n, false
     else
       (* let () = Printf.printf " not keeping it\n"in *)
       Some "", false
  | ArrayAccess {array; index} ->
     begin
       match index with
       | _, Int (_, i) ->
          begin
            match acc_members ~name (snd array) with
            | None, b -> None, b
            | Some res, b ->
               Some (res ^ "[" ^ Bigint.to_string i.value ^ "]"), b
          end
       | _ -> failwith ("Error :: indices must be integer literals at " ^ Petr4.Info.to_string (fst index))
     end
  | _ -> None, false
    

  
let is_parser prog name =
  let Program decls = prog in
  List.fold decls ~init:false
    ~f:(fun acc decl ->
      if acc then acc else
      match decl with
      | Declaration (_, Parser p ) ->
         if snd p.name = name then true else acc
      | _ -> acc
    )

let is_control prog name =
  let Program decls = prog in
  List.fold decls ~init:false
    ~f:(fun acc decl ->
      if acc then acc else
        match decl with
        | Declaration (_, Control c) ->
           if snd c.name = name then true else acc
        | _ -> acc
    )
  
  
let get_parser_name prog args =
  let Program decls = prog in
  List.fold args ~init:None ~f:(fun acc (_, arg) ->
      let open Argument in
      match arg with
      | Expression e ->
         Expression.(match e.value, acc with
                     | (_,NamelessInstantiation {typ; args}), None ->
                        begin
                          let open Type in
                          match typ with
                          | (_,TypeName (_, name)) -> 
                             if is_parser prog name then
                               Some name
                             else
                               None
                          | _-> None
                        end
                     | _, _ -> acc )
      | _ -> acc)
  
      
let get_pipeline_names prog args =
  let Program decls = prog in
  List.fold_left args ~init:[]
    ~f:(fun acc (_, arg) ->
      let open Argument in
      match arg with
      | Expression e ->
         Expression.(match e.value with
                     | (_, NamelessInstantiation {typ; args}) ->
                        begin
                          let open Type in
                          match typ with
                          | (_, TypeName (_,name)) ->
                             if is_control prog name then
                               acc @ [name]
                             else
                               acc
                          | _ -> acc
                        end
                     | _, _ -> acc
         )
      | _ -> acc
    )

  
let lookup_package prog pname =
  let Program decls = prog in
  List.fold decls ~init:None
    ~f:(fun pkg decl ->
      match pkg with
      | Some _ ->
         pkg
      | None ->
         let open Declaration in
         match decl with
         | TypeDeclaration _ -> pkg
         | Declaration (_, decl) ->
            let open Declaration in
            match decl with
            | Instantiation {annotations=_; typ=typ; args=args; name=(_,namestr)} ->
               if namestr = pname then
                 let open Option in
                 get_parser_name prog args >>= fun parsername ->
                 Some (parsername, get_pipeline_names prog args)
               else
                 (* let () = Printf.printf "Noting that %s != %s\n" namestr pname in *)
                 None
            | _ -> pkg
    )


  
let lookup_table prog ctx (tname:string) : Table.property list option =
  let open Declaration in
  let get_matching_table_opt table_opt decl =
    match table_opt, decl with
    | None, (_, Table t) ->
       (* Printf.printf "~~~~ Checking whether %s = %s ~~~~\n" (snd t.name) tname; *)
       if (snd t.name) = tname then
         (* let () = Printf.printf "\t it does\n" in *)
         Some t.properties
       else
         (* let () = Printf.printf "\t it does not \n" in *)
         table_opt
    | _ -> table_opt
  in
  let get_decl_opt d =
    let open TopDeclaration in
    match d with
    | Declaration d -> Some d
    | TypeDeclaration d -> None
  in
  match ctx with
  | (_, Control c) ->
     begin
       let local_tbl = List.fold c.locals ~init:None ~f:get_matching_table_opt in
       match local_tbl, prog with
       | Some _,_ -> local_tbl
       | None, Program(decls) ->
          List.filter_map decls ~f:get_decl_opt
          |> List.fold ~init:None ~f:get_matching_table_opt
     end
         
  | _ -> failwith ("ERROR :: Tried to Lookup table in non-control declaration " ^ snd (name ctx))
     

let typ_of_typ_map m = 
  String.Map.data m |> List.fold_left ~init:Type.empty ~f:Type.union

                 
let parser_env (p : program) : string option * (int * int) HMap.t =
  let open TopDeclaration in
  let Program decls = p in
  let f acc decl =
    match decl with
    | Declaration (_, Instantiation i) ->
       begin
         match i.typ with
         | (_, HeaderStack hs) ->
            HMap.add_exn acc ~key:(name_of_inst i.name None) ~data:(0, int_of_expr hs.size)
         | _ ->
            HMap.add_exn acc ~key:(name_of_inst i.name None) ~data:(0, 1)
       end
    | _ -> acc
  in
  (None, List.fold_left decls ~init:HMap.empty ~f:f)

let check_valid all typ hdr =
  (* hdr \in all -> typ |- hdr *)
  (* let () = Printf.printf "Headers: ";
   *          List.iter (HSet.to_list all) ~f:(fun h -> Printf.printf "%s " h);
   *          Printf.printf "\n%!" in *)
  not (HSet.mem all hdr) || Type.valid typ hdr

(* let colorize (attrs:Console.Ansi.attr list) (s:string) : string =
 *   Console.Ansi.string_with_attr attrs s *)

let warning_str : string=
  let open ANSITerminal in
  sprintf [yellow] "warning"

let error_str =
  let open ANSITerminal in
  sprintf [red] "error"
  
let format_t (info : Petr4.Info.t) : string = Petr4.Info.to_string info
  
let warn_assume_valid info name act =
  Format.eprintf "@[%s: %s: assuming %s matched as valid for rules with action %s@\n@]%!" (format_t info) warning_str name act
  
let warn_uninhabited info ~msg =
  Format.eprintf "@[%s: %s: type is uninhabited%s@\n@]%!" (format_t info) warning_str (if msg <> "" then " " ^ msg else msg)

let warn_assume_valid info str act =
  Format.eprintf "@[%s: %s: assuming %s matched as valid for rules with action %s@\n@]%!" (format_t info) warning_str str act

let warn_assume_masked info hdr str =
  Format.eprintf "@[%s: %s: assuming either %s matched as valid or %s wildcarded@\n@]%!" (format_t info) warning_str hdr str


  
let assert_valid info typ hdr = 
  Format.eprintf "@[%s: %s: %s not guaranteed to be valid@\n@]%!" (format_t info) error_str hdr


let stack_size prog typstr : int option =
  let Program(decls) = prog in
  List.fold_left decls ~init:None ~f:(fun acc decl ->
      match acc with
      | Some max -> acc
      | None ->
         begin
           let open TopDeclaration in
           let open TypeDeclaration in
           match decl with
           | TypeDeclaration (_, Struct {annotations; name; fields} ) ->
              if snd name = "headers" then
                List.fold fields ~init:None ~f:(fun acc (info, field) ->
                    if snd field.name = typstr then
                      match field.typ with
                      | (_, HeaderStack {header; size}) ->
                         let open Expression in
                         begin
                           match snd size with
                           | Int (_,p4int) -> (Bigint.to_int p4int.value)
                           | _ -> failwith ("Error :: stack size must be integer literal at " ^ Petr4.Info.to_string (fst size))
                         end
                      | _ -> acc
                    else acc
                  )
              else
                acc
           | _ -> acc
         end
    )

  
let rec find_available_index ?start:(start=0) prog (all : HSet.t) typ typstr =
  (* Printf.printf "Finding smallest available index for %s, currently on %d\n%!" typstr start; *)
  let typstr' = typstr ^ "[" ^ Int.to_string start ^ "]" in
  if HSet.mem all typstr' && Type.(valid typ typstr') then
    (* let () = Printf.printf "%s is valid in type\n%!" typstr' in *)
    find_available_index ~start:(start + 1) prog all typ typstr
  else
    let open Option in
    stack_size prog typstr >>= fun size ->
    if start >= size then
      None
    else
      Some start
  
let rec check_parser_stmt prog (ctx : Declaration.t) (all : HSet.t) (penv : string option * (int * int) HMap.t) stmt typ =
  let open Statement in
  let open Expression in
  let open Type in
  (* Format.printf "Checking Parser Statement at %s\n at type type:\n\t" (Petr4.Info.to_string (fst stmt));
   * Type.format Format.std_formatter typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n"; *)
  (* Printf.printf "Checking parser statement at %s \n%!" (Petr4.Info.to_string (fst stmt)); *)
  match snd stmt with
  | MethodCall {func=func; type_args=type_args; args=args} ->
     (* Do we need to do something with type_args? *)
     (* Printf.printf "Its a Method Call\n%!"; *)
     begin
       match func with
       | (info, ExpressionMember {expr=_; name=name}) ->
          if snd name = "extract" then
            match args with
            | [] -> Some (penv, typ)
            | [(_,hdr)] ->
               begin
                 let open Argument in
                 match hdr with
                 | Expression {value} ->
                    begin
                      match snd value with
                      | ExpressionMember {expr; name=(_,curr)} ->
                         begin
                           let wrk_exp = if curr = "next" then
                                           (* let () = Printf.printf "Processing stack\n%!"in *)
                                           expr
                                         else value
                           in
                           match fst (acc_members ~name:false (snd wrk_exp)) with
                           | None -> failwith ("ERROR :: could not extract member from  "
                                               ^ Petr4.Info.to_string (fst wrk_exp))
                           | Some typstr ->
                              if curr = "next" then
                                match find_available_index prog all typ typstr with
                                | None -> (*no available index for the header*)
                                   (* Printf.printf "Warning :: No available index for %s, returning None\n%!" typstr; *)
                                   None
                                | Some idx ->
                                   let typstr_idx = typstr ^ "[" ^ Int.to_string idx ^ "]" in
                                   let penv' = (Some typstr_idx, snd penv) in
                                   let typ' = Type.(add typ typstr_idx) in
                                   Some (penv', typ')
                              else
                                let penv' = (Some typstr, snd penv) in
                                let typ' = Type.(add typ typstr) in
                                Some (penv', typ')
                         end
                      | ArrayAccess {array; index} ->
                         begin
                           match fst (acc_members ~name:false (snd array)), index with
                           | None, _-> failwith ("ERROR :: couldn't find member from expression at " ^ (Petr4.Info.to_string (fst array)))
                           | Some mem, (_, Int (_, i)) ->
                              let typstr = mem ^ "[" ^ (Bigint.to_string i.value) ^ "]" in
                              Some(penv, Type.add typ typstr)
                           | Some mem, (info,_) -> failwith ("Error :: Array access not an integer literal at " ^ Petr4.Info.to_string info)
                         end
                      | _ -> failwith ("ERROR :: unrecognized header at " ^ Petr4.Info.to_string info)
                    end
                 | Missing -> failwith "Missing argument!"
                 | KeyValue _ -> failwith "Cannot extract via Key-Value"
               end
            | _ -> failwith "Cannot extract multiple headers at once"
          else failwith ("TODO:: Unrecognized method " ^ snd name)
       | _ -> failwith ("Method Called on a Non-member expression")
     end
  | Assignment a ->
     (* let () = Printf.printf "Its an Assignment \n%!" in *)
     Some (penv, 
      typ
      |> check_parser_expr prog all penv a.rhs
      |> check_parser_expr prog all penv a.lhs)
  | DirectApplication {typ=cp_typ; args=args} ->
     (* let () = Printf.printf "Its a Direct Application \n" in     
      * let lookfor typestr =
      *   match lookup_parser_state prog (snd (Declaration.name ctx)) typestr with
      *   | Some (_,pstate) -> check_parser_state prog ctx all penv pstate typ
      *   | None -> match lookup_control_state prog typestr with
      *             | Some parser -> failwith "Do not know how to mingle control and parsing"
      *             | None -> failwith ("Could not find " ^ typestr)
      * in *)
     (* begin
      *   match cp_typ with
      *   | (_, TopLevelType (_, typestr) ) 
      *     | (_, TypeName (_, typestr) ) ->
      *      Option.(lookfor typestr >>= fun typ -> Some(penv, typestr))
      *   | (_, _) -> failwith "Dont know how to apply that type"
      * end *)
     failwith ("Error Cannot Handle direct application at " ^ Petr4.Info.to_string (fst stmt))
     
  | Conditional {cond=cond; tru=tru_stmt; fls=fls_stmt} ->
     (* let () = Printf.printf "Its a Conditional\n%!" in *)
     Some (penv, 
      check_conditional_stmt prog ctx all [] cond tru_stmt fls_stmt typ)
  | BlockStatement {block = block} ->
     (* let () = Printf.printf "Its a Block\n%!" in *)
     Some (penv, check_block prog ctx all [] block typ)
  | Exit -> Some (penv, typ)          
  | EmptyStatement -> Some (penv,typ)
  | Return {expr=None} -> Some (penv, typ)
  | Return {expr=Some e} -> (* Printf.printf "RETURNING SOMEWHERE?\n%!"; *)
                            Some (penv, check_parser_expr prog all penv e typ)
  | Switch sw ->
     Some (penv, 
      typ
      |> check_expr prog all [] sw.expr
      |> check_switch_cases prog ctx all [] sw.cases)
  | DeclarationStatement decl ->
     failwith ("Error ::Don't know how to handle local declarations at" ^ Petr4.Info.to_string (fst stmt))
    


and check_arg prog all (valids : string list) arg typ =
  let open Argument in
  match arg with
  | (_, Expression      {value=e}) 
    | (_, KeyValue {key=_; value=e}) ->
     check_expr prog all valids e typ
  | _ -> typ


and check_args prog all (valids : string list) args typ =
  List.fold_left args ~init:typ
    ~f: (fun typ arg ->
      check_arg prog all valids arg typ
    )


(* [valids] is the list of valid bits in a table application*)
and check_expr prog all (valids : string list) expr ?act:(act="") typ =
  let open Expression in
  (* Printf.printf "Checking expr with valids: ";
   * List.iter valids ~f:(Printf.printf "%s ");
   * Printf.printf "\n%!"; *)
  let do_valid_check ?stack:(stack=false) info name typ =
    if not (check_valid all typ name) then
      (* let () = Printf.printf "-----invalid\n%!" in *)
      if List.mem valids name ~equal:(=) then
        begin
          let pos_typ = Type.restrict typ name in
          if not (Type.contradiction pos_typ) then
            begin
              warn_assume_valid info name act;
              pos_typ
            end
          else
            begin
              assert_valid info typ name;
              typ
            end
        end
      else
        begin
          assert_valid info typ name;
          typ
        end
    else
      (* let () = Printf.printf "~~~valid\n%!" in *)
      typ
  in
  let (info,e) = expr in
  match e with
  | True -> typ
  | False -> typ
  | Int i -> typ
  | String s -> typ
  | Name (info,name) ->
     do_valid_check info name typ
  | TopLevel (info, name) ->
     (* TODO :: CHECK this *)
     do_valid_check info name typ
  | ArrayAccess {array=a; index=i} ->
     typ
     |> check_expr prog all valids i ~act:act
     |> check_expr prog all valids a ~act:act
    
  | BitStringAccess {bits=bs; lo=l; hi=h} ->
     typ
     |> check_expr prog all valids l ~act:act
     |> check_expr prog all valids h ~act:act
     |> check_expr prog all valids bs ~act:act

  | List {values=vs} ->
     List.fold_left vs
       ~init:typ
       ~f:(fun typ v -> check_expr prog all valids v typ ~act:act)

  | UnaryOp {op=op; arg=e} ->
     check_expr prog all valids e typ
    
  | BinaryOp {op=_; args=(e,e')} ->
     typ
     |> check_expr prog all valids e ~act:act
     |> check_expr prog all valids e' ~act:act
    
  | Cast {typ=_; expr=e} ->
     check_expr prog all valids e typ ~act:act
    
  | TypeMember _ ->
     Printf.printf "Warning :: Do not know how to handle type members at %s... ignoring\n%!"
       (Petr4.Info.to_string info);
     typ
  | ErrorMember s -> failwith "TODO :: check_expr case ErrorMember"
  | ExpressionMember {expr=(info,e); name=n} ->
     if snd n = "action_run" then
       failwith ("ERROR (UnsupportedFunctionality) :: [action_run] hit analysis at " ^ (Petr4.Info.to_string info))     else
     begin
       match acc_members e ~name:false with
       | None,_ -> failwith ("TODO :: could not extract expression at " ^ Petr4.Info.to_string info)
       | Some mem, true ->
          begin
          match find_available_index prog all typ mem  with
          | None ->
             (* none means index >= stack size*)
             typ
          | Some 0 ->
             (* 0 members of stack have been initialized*)
             assert_valid info typ (mem ^ "[0]"); typ
          | Some _ ->
             typ
          end
       | Some mem, false ->
          (* Printf.printf "[check_expr] Checking validity of %s\n%!" mem; *)
          do_valid_check info mem typ
     end
  | Ternary {cond=cond; tru=tru_expr; fls=fls_expr} ->
     ignore (check_expr prog all [] cond typ);
     let tru_typ, fls_typ = partition_typ_expr typ cond in
     let tru_typ' =
       if Type.contradiction tru_typ then
         (warn_uninhabited info ~msg:"in true branch"; tru_typ)
       else
         check_expr prog all [] tru_expr tru_typ 
     in
     let fls_typ' =
       if Type.contradiction fls_typ then
         (warn_uninhabited info ~msg:"in false branch"; fls_typ)
       else
         check_expr prog all [] fls_expr fls_typ
     in

     Type.union tru_typ' fls_typ'
     
  | FunctionCall {func=f; type_args=typs; args=args} ->
     (* begin
      *   match is_validity_expr f with
      *   | (true, None) -> failwith ( "Error :: could not get header from validity check at " ^ Petr4.Info.to_string info)
      *   | (true, Some mem) -> Type.(restrict typ mem)
      *   | (false, _) -> failwith ("TODO lookup function call f from " ^ Petr4.Info.to_string info)
      * end *)
    typ
  | NamelessInstantiation {typ=_; args=args} ->
     check_args prog all valids args typ
  | Mask {expr=e; mask=m} ->
     typ
     |> check_expr prog all valids m ~act:act
     |> check_expr prog all valids e ~act:act
  | Range {lo=lo; hi=hi} ->
     typ
     |> check_expr prog all valids lo ~act:act
     |> check_expr prog all valids hi ~act:act
    
and check_parser_expr prog all penv ?act:(act="") (expr:Expression.t) (typ : Type.t) : Type.t =
  check_expr prog all [] ~act:act expr typ

and check_control_expr prog ctx all valids ?act:(act="") (expr:Expression.t) (typ : Type.t) : Type.t =
  check_expr prog all valids ~act:act expr typ
  
and check_parser_match prog all penv (m : Match.t) typ : Type.t =
  match m with
  | (_, Match.Expression e) ->
     check_parser_expr prog all penv e.expr typ
  | _ -> typ
       
and check_parser_matches (prog : program) all (penv : string option * (int * int) HMap.t) (matches : Match.t list) typ : Type.t =
  List.fold_left matches
    ~init:typ
    ~f:(fun acc m -> check_parser_match prog all penv m typ)
  
  
and check_parser_case (prog : program) ctx all (penv : string option * (int * int) HMap.t) (case:Parser.case) typ : Type.t =
  let (_,c) = case in
  let typ = check_parser_matches prog all penv c.matches typ in
  if snd c.next = "accept" then
    typ
  else if snd c.next = "reject" then
    Type.empty
  else
    match lookup_parser_state prog (snd (Declaration.name ctx)) (snd c.next) with
    | None -> failwith ("Couldnt find parser state " ^ (snd c.next))
    | Some (_,next_hop) ->
       (* Printf.printf "Hopping to %s\n%!" (snd c.next); *)
       match check_parser_state prog ctx all penv next_hop typ with
       | None -> (* behave as if reject *)
          Type.empty
       | Some typ ->  typ
    
    
and check_parser_statements (prog : program) ctx (all_hdrs : HSet.t) (penv : string option * (int * int) HMap.t) stmts typ : Type.t option =
  let open Option in
  List.fold_left stmts
    ~init:(Some (penv, typ))
    ~f:(fun acc_opt stmt ->
      acc_opt >>= fun (penv, typ) ->
      check_parser_stmt prog ctx all_hdrs penv stmt typ
    )  >>= fun (penv', typ') -> Some typ'


  
and check_parser_exprs prog all (penv : string option * (int * int) HMap.t) exprs typ =
  List.fold_left exprs ~init:typ
    ~f:(fun typ expr -> check_parser_expr prog all penv expr typ)

and check_cases prog ctx all (penv : string option * (int * int) HMap.t) cases typ =
  (* Printf.printf "Checking %d cases \n%!" (List.length cases); *)
  List.fold_left cases
    ~init:(Type.empty)
    ~f:(fun acc case ->
      check_parser_case prog ctx all penv case typ
      |> Type.union acc
    )
  
and check_transition prog ctx (all : HSet.t) (penv : string option * (int * int) HMap.t) trans typ : Type.t option=
  begin
    let open Parser in
    match trans with
    | (_, Direct {next=(_,n)}) -> 
       if n = "accept" then
         Some typ
       else if n = "reject" then
         Some Type.empty
       else
         begin 
           match lookup_parser_state prog (snd (Declaration.name ctx)) n  with
           | None -> failwith ("Couldn't find parser state " ^ n)
           | Some (_, next_hop) ->
              check_parser_state prog ctx all penv next_hop typ
         end
    | (_, Select {exprs=es; cases=cs}) ->
       Some (typ
       |> check_parser_exprs prog all penv es
       |> check_cases prog ctx all penv cs)
      
  end
  
and check_parser_state (prog : program) (ctx : Declaration.t) (all_hdrs : HSet.t) (penv : 'a option * (int * int) HMap.t) (state : Parser.state) typ : Type.t option=
  let open Parser in
  let open Option in
  let (_, s) = state in
  (* TODO :  FIGURE OUT PARSER TERMINATION -- should be the same solution to recirculate *)
  (* Printf.printf "Checking Parser %s at state %s\n%!"
   *   (snd (Declaration.name ctx))
   *   (snd (snd state).name); *)
  check_parser_statements prog ctx all_hdrs penv s.statements typ
  >>= check_transition prog ctx all_hdrs penv s.transition

  
  
and check_block prog ctx (all : HSet.t) (valids : string list) (block : Block.t) typ : Type.t =
  let open Block in 
  let (info, b) : Block.t = block in
  List.fold_left b.statements
    ~init:typ
    ~f:(fun typ' stmt ->
      check_control_stmt prog ctx all valids stmt typ'
    )

and check_switch_case prog (ctx : Declaration.t) (all : HSet.t) (valids : string list) (c : Statement.switch_case) typ =
  match c with
  | (_, FallThrough _) ->
     typ
  | (_, Action {label=_; code=block}) ->
     check_block prog ctx all valids block typ
    
and check_switch_cases prog (ctx : Declaration.t) (all : HSet.t) (valids : string list) (cs : Statement.switch_case list) typ : Type.t =
  List.fold_left cs ~init:Type.empty
    ~f:(fun t c -> check_switch_case prog ctx all valids c t)



and check_conditional_stmt prog (ctx : Declaration.t) all (valids : string list) cond tru_ctrl fls_opt typ  =
  ignore (check_expr prog all [] cond typ);
  let tru_typ, fls_typ = partition_typ_expr typ cond in
  let tru_typ' =
    if Type.contradiction tru_typ then
      (warn_uninhabited (fst cond) ~msg:"in true branch"; tru_typ)
    else
      check_control_stmt prog ctx all valids tru_ctrl tru_typ 
  in
  let fls_typ' =
    match fls_opt with
    | None -> typ
    | Some fls_ctrl ->
       if Type.contradiction fls_typ then
         (warn_uninhabited (fst cond) ~msg:"in false branch"; fls_typ)
       else
         check_control_stmt prog ctx all valids fls_ctrl fls_typ
  in

  Type.union tru_typ' fls_typ'

(* RETURNS whether [expr] is a validity expression and the header checked to be valid *)
and is_validity_expr expr : bool * (string option) =
  let open Expression in
  match expr with
  | (_, FunctionCall {func=(_,func); type_args=[]; args=[]}) ->
     begin
       match func with
       | ExpressionMember {expr=(_,expr); name=name} ->
          if snd name = "isValid"
          then
            true, fst (acc_members ~name:false expr)
          else
            false, None
       | _ -> false, None
     end
  | _ -> false, None
       
and partition_typ_expr typ expr =
  let open Expression in
  match expr with
  | (_, BinaryOp {op=oper; args=(e1, e2)}) ->
    begin
      match oper with
      | (_, Op.And) ->
         let typ11, typ12 = partition_typ_expr typ e1 in
         let typ21, typ22 = partition_typ_expr typ11 e2 in
         Type.(typ21, union typ12 typ22)
      | (_, Op.Or) ->
         let typ11, typ12 = partition_typ_expr typ e1 in
         let typ21, typ22 = partition_typ_expr typ12 e2 in
         Type.(union typ11 typ21, typ22)
      | (_, _ ) -> (typ, typ)
    end
  | (_, UnaryOp {op=oper; arg= e1}) ->
     begin
       match oper with
       | (_, Op.Not) ->
          let typ11, typ12 = partition_typ_expr typ e1 in
          (typ12, typ11)
       | (_,_) -> (typ, typ)
     end
  | (_, FunctionCall {func=func; type_args=[]; args=[]}) ->
     begin
       match is_validity_expr func with
       | (true, Some hdrname) -> 
          Type.(restrict typ hdrname, neg_restrict typ hdrname)
       | (true, None) ->
          failwith "Error :: Could not extract header for isValid() call"
       | (false, _) ->
          (* TODO :: partition on called functions *)
          typ, typ
     end
  | (_, _) -> (typ, typ)
       
and unpack_table table =
  let open Table in
  List.fold table ~init:(([],[]),[],[],[])
    ~f:(fun ((valids,all_keys), actions, entries, customs) curr ->
      match curr with
      | (_, Key {keys=keys}) ->
         let (valids', all_keys') =
           List.fold (keys) ~init:(valids, all_keys)
             ~f:(fun (vs, ks) k ->
               let (is_valid, hdrstr_opt) = is_validity_expr (snd k).key in
               match hdrstr_opt with
               | Some hdr -> 
                  ( hdr :: vs, ks)
               | None -> 
                  ( vs, k :: ks)
             )
         in
         ((valids', all_keys'), actions, entries, customs)
      | (_, Actions {actions=actions'}) ->
         ((valids, all_keys), actions @ actions', entries, customs)
      | (_, Entries {entries=entries'}) ->
         ((valids, all_keys), actions, entries @ entries', customs)
      | (_, Custom c) ->
         ((valids, all_keys), actions, entries, customs @ [Custom c])
        
        
    )

and is_maskable mkind = snd mkind = "ternary" || snd mkind = "lpm"


and header_inst_of_expr expr =
  let open Expression in
  let open P4Int in
  let open Option in
  let error_msg str info =
    failwith ("Error :: Expected Name, ExpMember, ArrayAccess or Mask, got " ^ str ^ "instead at " ^ Petr4.Info.to_string info)
  in
  match expr with
  | (_, Name n) -> Some (snd n)
  | (_, ExpressionMember {expr=expr'; name=name}) ->     
     header_inst_of_expr expr' >>= fun acc_name ->
     Some ( acc_name ^ "." ^ snd name)
  | (_, ArrayAccess {array; index}) ->
     begin
       match index with
       | (_, Int (_,p4int)) ->
          header_inst_of_expr array >>= fun array_name ->
          Some (array_name ^ "[" ^ Bigint.to_string p4int.value ^ "]")
       | (_, Expression.Range {lo=(_, Int (_, intlo));
                               hi=(_, Int (_, inthi))}) ->
          header_inst_of_expr array >>= fun array_name ->
          Some (array_name ^ "[" ^ Bigint.to_string intlo.value
                ^ ":" ^ Bigint.to_string inthi.value ^ "]")
       | (index_info, _) ->
          failwith ("Error :: Index into header stack must be integer literal or range at " ^ Petr4.Info.to_string index_info)
     end
  | (_, Mask m) ->
     header_inst_of_expr m.expr
  | (info, BitStringAccess {bits;
                            lo=(_, Int(_, intlo));
                            hi=(_, Int(_, inthi))}) ->
     header_inst_of_expr bits >>= fun bits_name ->
     Some (bits_name ^ "["
           ^ Bigint.to_string intlo.value ^ ":" ^
             Bigint.to_string inthi.value ^ "]")

  | (info, List _) -> error_msg "List" info
  | (info,_) -> error_msg "??" info

and check_table_key prog all valids typ (key : Table.key) =
  let open Table in
  let (info, k) = key in
  if fst (is_validity_expr k.key) then
    ()
  else
    match header_inst_of_expr k.key with
    | None -> failwith ("Error :: Key must be a headerfield at " ^ Petr4.Info.to_string info)
    | Some hdrstr -> 
       if HSet.mem all hdrstr && not (Type. valid typ hdrstr) then
         begin
           if is_maskable k.match_kind && List.mem valids hdrstr ~equal:(=) then
             warn_assume_masked info hdrstr hdrstr
           else
             assert_valid info typ hdrstr
         end
       else ()

and check_table_action prog ctx all valids typ (act : Table.action_ref) =
  let open Table in
  let str = snd ((snd act).name) in
  (* let () = Printf.printf "Checking %s with valids: " str;
   *          List.iter valids ~f:(Printf.printf "%s ");
   *          Printf.printf "\n%!"
   * in *)
  let action_body = lookup_action_function prog ctx str in
  match action_body with
  | Some (_, Action a) ->  (str, check_block prog ctx all valids a.body typ)
  | None -> failwith ("Error :: Could not find action "
                      ^ str ^ " in control "
                      ^ snd (Declaration.name ctx)
                      ^ " at " ^ (Petr4.Info.to_string (fst act)))
  | _ -> failwith "Error Expected Action as result of [lookup_action_function]"
  
and check_table_actions prog ctx all valids typ (actions : Table.action_ref list) =
  let open Table in
  List.fold_left actions ~init:String.Map.empty
    ~f:(fun acc act ->
      let str, typ = check_table_action prog ctx all valids typ act in
      String.Map.add_exn acc str typ
    )

and check_matches prog all (typ : Type.t) matches =
  List.fold_left matches ~init:typ
    ~f:(fun typ' (_, mexpr) ->
      let open Match in
      match mexpr with
      | Expression {expr=expr} ->
         check_expr prog all [] expr typ'
      | Default | DontCare ->
         typ'
    )
  
and check_entries prog ctx all valids typ entries =
  List.fold_left entries ~init:typ
    ~f:(fun acc entry ->
      let open Table in
      match entry with
      | (_, {annotations=_; matches=matches; action = action} ) ->
         let open Declaration in
         let (_,act_name) = (snd action).name in
         match lookup_action_function prog ctx act_name with
         | None -> failwith ("ERROR :: Could not find " ^ act_name ^ " in context " ^ snd (name ctx))
         | Some (_,Action a) ->
            check_matches prog all typ matches
            |> check_block prog ctx all valids a.body
         | _ -> failwith "ERROR :: Expected [lookup_action_function] to return a function declaration"
    )

  
and check_table (info : Petr4.Info.t) prog ctx all typ tbl =
  let open Table in
  let (valids,all_keys), actions, entries, customs = (* TODO :: Figure out customs *)
    unpack_table tbl in
  List.iter all_keys ~f:(check_table_key prog all valids typ);
  (* Printf.printf "valids : ";  List.iter valids ~f:(fun f -> Printf.printf "%s " f); Printf.printf "\n%!"; *)
  let acts_typ_map = check_table_actions prog ctx all valids typ actions in
  let def_typ = 
    (* TODO Default action not supported in grammar? *)
    typ (* Default default_action is nop *)
  in
  let ent_typ = check_entries prog ctx all valids typ entries in
  (acts_typ_map, def_typ, ent_typ)


and get_locals decl =
  let open Declaration in
  match decl with
  | (_,Control c) -> c.locals
  | (_,Parser  p) -> p.locals
  | _ -> failwith ("ERROR :: Tried to get locals from " ^ snd (name decl) ^ " but " ^ snd(name decl) ^ " is neither a control nor a parser")
  

(** Optionally Return the expression indicating which table to apply *
   return None when the expression isnt an [action_run] or could not
   find the base table
 *)

and get_action_run_table_name switch : Expression.t option =
  let open Expression in
  match switch with
  | (_, ExpressionMember {expr; name}) ->
     if snd name = "action_run" then
       let open Expression in
       let error_msg inf = failwith ("ERROR :: Couldnt figure out what you wanted to [action_run] at " ^ (Petr4.Info.to_string inf)) in
       match snd expr with
       | FunctionCall { func=(info,ExpressionMember {expr=tbl_expr; name});
                        type_args=[];
                        args=[]} ->
          if snd name = "apply" then
            Some tbl_expr
          else
            error_msg info
       | _ -> error_msg (fst expr)
     else
       None
  | _ -> None


and check_action_run_case prog ctx all acts_typ_map def_typ case typ =
  let open Statement in
  match case with
  | (info,FallThrough _) ->
     failwith ("Error :: all cases must be explicit " ^ Petr4.Info.to_string info)
  | (info, Action {label; code}) ->
     match label with
     | (_, Default) ->
        check_block prog ctx all [] code def_typ
     | (_, Name (info, name)) -> 
        Map.find_exn acts_typ_map name
        |> check_block prog ctx all [] code
       
and check_action_run_cases prog ctx all acts_typ_map def_typ cases typ =
  List.fold_left cases ~init:Type.epsilon ~f:(fun acc_typ case ->
      check_action_run_case prog ctx all acts_typ_map def_typ case typ
    )
       
and check_action_run prog ctx all tbl_to_apply cases typ : Type.t =
  let open Expression in
  match tbl_to_apply with
  | (tbl_call_info, Name (name_info,tbl_name)) ->
     begin
     match lookup_table prog ctx tbl_name with
     | None -> failwith ("Error :: Could not find table [" ^ tbl_name ^ "], invoked from " ^ Petr4.Info.to_string name_info)
     | Some tbl_props ->
        let acts_typ_map, def_typ, ent_typ = check_table name_info prog ctx all typ tbl_props in
        typ
        |> check_action_run_cases prog ctx all acts_typ_map def_typ cases
        |> Type.union def_typ
        |> Type.union ent_typ
        
     end
  | (tbl_call_info,_) -> failwith ("Error :: Don't know which table to call at " ^ Petr4.Info.to_string tbl_call_info )
  
       
and check_control_stmt prog ctx all valids (stmt : Statement.t) typ : Type.t=
  let open Statement in
  let (info, s) = stmt in
  (* Printf.printf "%s , Checking control stmt with |typ| = %d\n%!" (Petr4.Info.to_string info) (Type.size typ); *)
  match s with
  | MethodCall m ->
     ignore (check_args prog all valids m.args typ);
     begin
       match m.func with
       | (_, ExpressionMember {expr=(expr_info,expr); name=mname}) ->
          begin
            match snd mname with
            | "apply" ->
               begin
                 match expr with
                 | Name object_name ->
                    begin
                      match lookup_table prog ctx (snd object_name) with
                      | None -> (* Its not a table.. is it a locally defined control?*)
                         let open Declaration in
                         let open TopDeclaration in
                         begin
                           match lookup_control_instance prog ctx (snd object_name) with
                           | None -> failwith ("Could not resolve name " ^ snd object_name)
                           | Some ((_, Control c) as ctrl_ctx)  ->
                              check_block prog ctrl_ctx all valids c.apply typ
                           | _ -> failwith "ERROR :: expected control from [lookup_control_instance]"
                         end
                      | Some table ->
                         (* let () = Printf.printf "Checking table %s\n%!" (snd object_name) in *)
                         let acts_typ_map, def_typ, ent_typ = check_table info prog ctx all typ table in
                         (* Type.format Format.std_formatter ent_typ;
                          * Format.printf "@]%!\n";
                          * Printf.printf "\n"; *)
                         Type.(union (typ_of_typ_map acts_typ_map) def_typ |> union ent_typ)
                    end
                 | _ -> failwith "TODO APPLYING SOMETHING OTHER THAN A TABLE OR CONTROL"
               end
            | "setValid" ->
               begin
                 match fst (acc_members ~name:false expr) with
                 | None ->
                    failwith "Tried to setValid, but couldn't find a header to envalidate"
                 | Some hdrstr ->
                    Type.(add typ hdrstr)

               end
            | "setInvalid" ->
               begin
                 match fst (acc_members expr) with
                 | None -> failwith "Tried to setInvalid, but couldn't find a header to invalidate"
                 | Some hdrstr -> Type.(remove typ hdrstr)
               end
            | "emit" | "count" | "execute_meter" | "read" ->
               typ
            | "push_front" | "push_back" ->
               begin
               match fst(acc_members ~name:false expr) with
               | None -> failwith ("Error :: Tried to [" ^ snd mname ^ "], but could not figure out what you wanted to push at" ^ Petr4.Info.to_string expr_info)
               | Some mem ->
                  let idx_to_add = (find_available_index ~start:0 prog all typ mem) |> Option.value ~default:0 in
                  (* TODO ::  FIND ALL AND INCREMENT EACH *)
                  mem ^ "[" ^ Int.to_string idx_to_add ^ "]" |> Type.add typ

               end
            | action -> match lookup_action_function prog ctx action with
                        | Some (_, Action act) ->
                           check_block prog ctx all valids act.body typ
                        | None ->
                           failwith ("ERROR :: Could not find action " ^ action
                                     ^ " at " ^ (Petr4.Info.to_string info))
                        | _ ->
                           failwith "ERROR :: expected action from [lookup_action_function]"
          end
       | (_, Name n) ->
          (* if snd name *) 
          let open Declaration in
          begin
            match lookup_action_function prog ctx (snd n) with
            | Some (_,Action a) -> check_block prog ctx all valids a.body typ
            | Some (info,_) -> failwith ("ERROR :: Expected to find Action [" ^ snd n ^ "], but it was something else at " ^ Petr4.Info.to_string info )
            | None -> 
               Printf.printf "WARNING:: Unknown name [%s] when checking control statement at %s\n%!" (snd n) (Petr4.Info.to_string info);
               typ
          end
       | _ -> failwith ("ERROR : method call must be to a member or a name at " ^ Petr4.Info.to_string info)
     end
    
  | Assignment a ->
     typ
     |> check_control_expr prog ctx all valids a.rhs
     |> check_control_expr prog ctx all valids a.lhs
  | DirectApplication {typ=cp_typ; args=args} ->
     let lookfor typestr =
       match lookup_control_instance prog ctx typestr with
       | Some control -> check_control prog all control typ
       | None -> failwith ("Could not find control " ^ typestr)
     in
     begin
       match cp_typ with
       | (_, TopLevelType (_, typestr) ) 
         | (_, TypeName (_, typestr) ) -> lookfor typestr
       | (_, _) -> failwith "Dont know how to apply that type"
     end
     
  | Conditional {cond=cond; tru=tru_ctrl; fls=fls_opt } ->
     check_conditional_stmt prog ctx all valids cond tru_ctrl fls_opt typ
  | BlockStatement {block=b} ->
     check_block prog ctx all valids b typ
  | Return {expr=None} ->
     typ
  | Return {expr=(Some e)} ->
     check_control_expr prog ctx all valids e typ
  | Switch {expr=e; cases=cs} ->
     begin
     match get_action_run_table_name e with
     | Some tbl_to_apply ->
        check_action_run prog ctx all tbl_to_apply cs typ
     | None -> 
        typ
        |> check_control_expr prog ctx all valids e
        |> check_switch_cases prog ctx all valids cs
     end    
  | DeclarationStatement decl ->
     failwith "Match on declaration -- Error on instantiation!!! check Variable"
  | Exit -> typ
  | EmptyStatement -> typ
                    

and check_control prog all (ctrl : Declaration.t) typ =
  let open Declaration in
  match ctrl with 
  | (_, Control c) -> check_block prog ctrl all [] c.apply typ
  | _ -> failwith ("Expected Control, got " ^ snd (name ctrl) ^ " which is not a control declaration")
       

       
and check_prog (prog : program) : Type.t option =
  let open Option in
  (*Lookup parser name, lookup control name(s) and check them in
     sequence, according to package named "main"*)
  (* Printf.printf "Get the parser environment\n%!"; *)
  let penv = parser_env prog in
  (* Printf.printf "Gotten\n%!"; *)
  (* Printf.printf "searching for main\n%!"; *)
  let main_package = lookup_package prog "main" in
  (* Printf.printf "concluded search, matchin\n%!"; *)
  
  match main_package with
  | None -> failwith "Couldn't find main package"
  | Some (parser_name, pipeline_names) ->
     (* Printf.printf ">>>>>Getting instances\n%!"; *)
     let all = all_insts prog "headers" in
     (* Printf.printf "<<<<<gotten %d instances\n%!" (HSet.length all); *)
     lookup_parser_state prog parser_name "start"
     >>= fun (prsr_ctx,start_state) ->
     (* Printf.printf "Found parser and start state\n%!"; *)
     Printf.printf "Analyzing %d pipeline stages\n%!" (List.length pipeline_names + 1);
     Printf.printf ">>>>>>Checking %s\n%!" parser_name;
     check_parser_state prog prsr_ctx all penv start_state Type.epsilon
     >>= fun prsr_typ ->
     Printf.printf "<<<<<< Checked %s, type has size %d \n%!" parser_name (Type.size prsr_typ);
     List.fold_left pipeline_names
       ~init:(Some prsr_typ)
       ~f:(fun typ_opt name ->
         Printf.printf ">>>>>>checking stage %s\n%!" name;
         lookup_control_state prog name >>= fun stage ->
         typ_opt >>= fun typ ->
         Printf.printf "Checking %s with type of size %d\n%!" name (Type.size typ);
         (* Type.format Format.std_formatter typ;
          * Format.printf "@]%!\n"; Printf.printf "\n"; *)
         let outtyp = check_control prog all stage typ in
         Printf.printf "<<<<<<<< Checked %s!\n%!" name;
         Some outtyp
       )
       
       
