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

(** Notes:
 * + Assumes V1Model: 
     - reads name of struct with headers from second parameter to the first parameter V1Model package constructor 
     - extern methods are hard-coded into [check_dispatch] (e.g. [execute_meter] or [count])
 * + Will Fail on [ErrorMembers]
 * + Fails on [TopLevel] expressions
 * + Skips over [extern]s
 * + No rules for [update_checksum], it always passes
 * + Makes a strong assumption about behavior of [stack.push_front(e)] method.
      - it finds the maximum valid header index [i] and adds [stack[i+1]] to the type
      - The correct way to handle this is to traverse the type and increment every 
        found index [stack[i]] to [stack[i+1]], then add stack[0] to the type.
      - Both approaches are sound, but the "correct way" will reject fewer programs.
 *)

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
  val empty : t (* {} *)
  val epsilon : t (* {{}} *)
  val header : string -> t (*fun h -> {{h}}*)
  val concat : t -> t -> t (* fun t, t' -> { s U s'  | (s, s') in t x t' }  *)
  (* {eth}
   * if (eth.Ethertype == 0x800)
   * then extract(ipv4) ## concat (header "ipv4") {{"eth"}} = {{"eth", "ipv4"}}
   * else extract(ipv6) ## concat (header "ipv6") {{"eth"}} = {{"eth", "ipv6"}}
   * ## union {{"eth", "ipv4"}} {{"eth", "ipv6"}}
   *{{"eth", "ipv4"}, {"eth", "ipv6"}}
E*)
  val union : t -> t -> t 
  val restrict : t -> string -> t (* fun tau h -> { s | s in tau, h in s  }   *)
  val neg_restrict : t -> string -> t (* (fun tau h -> { s | s in tau, h not in s  }  *)
  val add : t -> string -> t (* concat (header "ipv4") {{"eth"}} = concat "ipv4" {{"eth"}}*)
  val remove : t -> string -> t (* fun tau h ->  { s \ h | s in tau} *)
  val copy : t -> string -> string -> t (* fun tau h h' -> { s[h|->h'] | s in tau }  *)
  val valid : t -> string -> bool (* fun tau h -> tau != {} && forall s in tau. h in s*)
  val contradiction: t -> bool (* fun tau -> tau == {} *)
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

  let format fmt t =
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

  let header h = UH.get (U.singleton (CH.get (C.singleton (H.get (String.strip h)))))

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
  let restrict = 
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

  let neg_restrict = 
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
    
  let remove = 
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

  let copy = 
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
         (* U != {} &&  for every t in U,  n in U *)
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
  
  let f acc (_, field) =
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
      | Some _ -> acc
      | None ->
         match decl with
         | TypeDeclaration (_, Struct{annotations=_; name; fields}) ->
            if snd name = header_struct_name then
              Some (List.fold_left fields ~init:HSet.empty ~f:f)
            else
              None
         | _ -> None
    ) |> Option.value ~default:HSet.empty
  

let value_exn_msg msg opt =
  match opt with
  | Some x -> x
  | None -> failwith msg

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
                        | Some _ ->
                           res
                      )
                else state
              | (_,_) -> None
          end )
  |> value_exn_msg ("Could not find state " ^ statename)

let lookup_action_function (prog : program) (decl : Declaration.t) (string:string) : Declaration.t option  =
  let open Declaration in
  match snd decl with
  | Control c ->
     begin
       let local_lookup = List.fold c.locals ~init:None
                            ~f:(fun func_opt decl' ->
                              match func_opt, decl' with
                              | Some _, _ -> func_opt
                              | None, ((_,Action a) as ainf) ->
                                 if snd a.name = string then
                                   Some ainf
                                 else
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
                                       

let lookup_control_state prog cname : Declaration.t =
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
    ) |> value_exn_msg ("Could not find control state " ^ cname)

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
                     match c.typ with
                     | _, (TypeName tn) ->
                        Some (lookup_control_state prog (snd tn))
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
  
let lookup_control_instance prog ctx iname : Declaration.t =
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
             lookup_control_state prog iname |> Some
     end
     |> value_exn_msg ("could not find control instance" ^ iname)
  | _ -> failwith "Error :: Expecting control got other type"
  
                   

let rec acc_members ?name:(name=true) ?stack_idx:(stack_idx=None) exp_mem : string option * bool =
  let open Expression in
  match exp_mem with
  | ExpressionMember {expr=(_,exp_mem'); name=name'} ->
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
  List.fold args ~init:None ~f:(fun acc (_, arg) ->
      let open Argument in
      match arg with
      | Expression e ->
         Expression.(match e.value, acc with
                     | (_,NamelessInstantiation {typ; args=_}), None ->
                        begin
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
  List.fold_left args ~init:[]
    ~f:(fun acc (_, arg) ->
      let open Argument in
      match arg with
      | Expression e ->
         Expression.(match e.value with
                     | (_, NamelessInstantiation {typ; args=_}) ->
                        begin
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
         match decl with
         | TypeDeclaration _ -> pkg
         | Declaration (_, decl) ->
            let open Declaration in
            match decl with
            | Instantiation {annotations=_; typ=_; args=args; name=(_,namestr)} ->
               if namestr = pname then
                 let open Option in
                 get_parser_name prog args >>= fun parsername ->
                 Some (parsername, get_pipeline_names prog args)
               else
                 (* let () = Printf.printf "Noting that %s != %s\n" namestr pname in *)
                 None
            | _ -> pkg)
  |> value_exn_msg ("could not find package" ^ pname)


  
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
    | TypeDeclaration _ -> None
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
  if Type.valid typ hdr then
    begin
      (* Printf.printf "VALID\n%!"; *)
      true
    end
  else if not (HSet.mem all hdr) then
    begin
      (* Printf.printf "VALID BECAUSE NOT A HEADER\n%!"; *)
      true
    end
  else
    begin
      (* Printf.printf "INVALID\n%!"; *)
      false
    end


let warning_str : string=
  let open ANSITerminal in
  sprintf [yellow] "warning"

let error_str =
  let open ANSITerminal in
  sprintf [red] "error"
  
let format_t (info : Petr4.Info.t) : string = Petr4.Info.to_string info
  
let warn_uninhabited info ~msg =
  Format.eprintf "@[%s: %s: type is uninhabited%s@\n@]%!" (format_t info) warning_str (if msg <> "" then " " ^ msg else msg)

let warn_assume_valid info str act =
  Format.eprintf "@[%s: %s: assuming %s matched as valid for rules with action %s@\n@]%!" (format_t info) warning_str str act

let warn_assume_masked info hdr str =
  Format.eprintf "@[%s: %s: assuming either %s matched as valid or %s wildcarded@\n@]%!" (format_t info) warning_str hdr str

let warn_no_index info hdr =
  Format.eprintf "@[%s: %s: parsed more elements of %s than allowed in the type! @\n@]%!" (format_t info) error_str hdr
  
let assert_valid info hdr = 
  Format.eprintf "@[%s: %s: %s not guaranteed to be valid@\n@]%!" (format_t info) error_str hdr


let stack_size prog typstr : int option =
  let Program(decls) = prog in
  List.fold_left decls ~init:None ~f:(fun acc decl ->
      match acc with
      | Some _ -> acc
      | None ->
         begin
           let open TopDeclaration in
           let open TypeDeclaration in
           match decl with
           | TypeDeclaration (_, Struct {annotations=_; name; fields} ) ->
              if snd name = "headers" then
                List.fold fields ~init:None ~f:(fun acc (_, field) ->
                    if snd field.name = typstr then
                      match field.typ with
                      | (_, HeaderStack {header=_; size}) ->
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
  
let rec check_parser_stmt (verbose_flag : bool ref) prog (ctx : Declaration.t) (all : HSet.t) (penv : string option * (int * int) HMap.t) stmt typ  =
  let open Statement in
  let open Expression in
  (* Format.printf "Checking Parser Statement at %s\n at type:\n\t" (Petr4.Info.to_string (fst stmt));
   * Type.format Format.std_formatter typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n"; *)
  (* Printf.printf "Checking parser statement at %s \n%!" (Petr4.Info.to_string (fst stmt)); *)
  match snd stmt with
  | MethodCall {func=func; type_args=_; args=args} ->
     ignore(check_args verbose_flag prog ctx all []  args typ);
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
                              Some (penv, Type.add typ typstr)
                           | Some _, (info,_) -> failwith ("Error :: Array access not an integer literal at " ^ Petr4.Info.to_string info)
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
    Some (penv, 
          typ
          |> check_parser_expr verbose_flag prog ctx all a.rhs
          |> check_parser_expr verbose_flag prog ctx all a.lhs)
  | DirectApplication {typ=_; args=_} ->
     failwith ("Error Cannot Handle direct application at " ^ Petr4.Info.to_string (fst stmt))
     
  | Conditional {cond=cond; tru=tru_stmt; fls=fls_stmt} ->
     (* let () = Printf.printf "Its a Conditional\n%!" in *)
    Some (penv, 
          check_conditional_stmt verbose_flag prog ctx all [] cond tru_stmt fls_stmt typ)
  | BlockStatement {block = block} ->
     (* let () = Printf.printf "Its a Block\n%!" in *)
    Some (penv, check_block verbose_flag prog ctx all [] block typ)
  | Exit -> Some (penv, typ)          
  | EmptyStatement -> Some (penv,typ)
  | Return {expr=None} -> Some (penv, typ)
  | Return {expr=Some e} -> (* Printf.printf "RETURNING SOMEWHERE?\n%!"; *)
                            Some (penv, check_parser_expr verbose_flag prog ctx all e typ)
  | Switch sw ->
    Some (penv, 
          typ
          |> check_expr verbose_flag prog ctx all [] sw.expr
          |> check_switch_cases verbose_flag prog ctx all [] sw.cases)
  | DeclarationStatement _ ->
    failwith ("Error ::Don't know how to handle local declarations at" ^ Petr4.Info.to_string (fst stmt))
    


and check_arg (verbose_flag : bool ref) prog ctx all (valids : string list) arg typ =
  let open Argument in
  match arg with
  | (_, Expression      {value=e}) 
    | (_, KeyValue {key=_; value=e}) ->
     check_expr verbose_flag prog ctx all valids e typ
  | _ -> typ


and check_args (verbose_flag : bool ref) prog ctx all (valids : string list) (args : Argument.t list) (typ : Type.t) : Type.t =
  List.fold_left args ~init:typ
    ~f: (fun typ arg ->
      check_arg verbose_flag prog ctx all valids arg typ
    )


(* [valids] is the list of valid bits in a table application*)
and check_expr (verbose_flag : bool ref) prog ctx all (valids : string list) expr ?act:(act="") typ =
  let open Expression in
  let do_valid_check info name typ =
    (* Format.printf "Checking Validity of %s\n in : " name;
     * Type.format Format.std_formatter typ;
     * Format.printf "@]%!\n";
     * Printf.printf "\n"; *)
    if check_valid all typ name then
      (* let () = Printf.printf "++++++++++++valid\n%!" in *)
      typ
    else
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
              assert_valid info name;
              typ
            end
        end
      else
        begin
          assert_valid info  name;
          typ
        end
  in
  let (info,e) = expr in
  match e with
  | True  | False | Int _ | String _  ->
     typ
  | Name (info,name) ->
     begin
     match lookup_action_function prog ctx name with
     | None -> typ
     | Some _ -> failwith ("name expression [" ^ name ^ "]is an action at  "^ Petr4.Info.to_string info)
     end
  | TopLevel (info, name) ->
     failwith ("Error :: Toplevel expression" ^ name ^" unsupported at " ^ (Petr4.Info.to_string info))
  | ArrayAccess {array=a; index=i} ->
     typ
     |> check_expr verbose_flag prog ctx all valids i ~act:act
     |> check_expr verbose_flag prog ctx all valids a ~act:act
    
  | BitStringAccess {bits=bs; lo=l; hi=h} ->
     typ
     |> check_expr verbose_flag prog ctx all valids l ~act:act
     |> check_expr verbose_flag prog ctx all valids h ~act:act
     |> check_expr verbose_flag prog ctx all valids bs ~act:act

  | List {values=vs} ->
     List.fold_left vs
       ~init:typ
       ~f:(fun typ v -> check_expr verbose_flag prog ctx all valids v typ ~act:act)

  | UnaryOp {op=_; arg=e} ->
     check_expr verbose_flag prog ctx all valids e typ
    
  | BinaryOp {op=_; args=(e,e')} ->
     typ
     |> check_expr verbose_flag prog ctx all valids e ~act:act
     |> check_expr verbose_flag prog ctx all valids e' ~act:act
    
  | Cast {typ=_; expr=e} ->
     check_expr verbose_flag prog ctx all valids e typ ~act:act
    
  | TypeMember _ ->
     Printf.printf "Warning :: Do not know how to handle type members at %s... ignoring\n%!"
       (Petr4.Info.to_string info);
     typ
  | ErrorMember _ -> failwith "ERROR (UnsupportedCommand) :: Cannot handle [ErrorMember]s"
  | ExpressionMember {expr=(info,e); name=n} ->
     (* let () = Printf.printf "CHECKING EXPRESSION MEMBER!\n%!" in *)
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
             assert_valid info (mem ^ "[0]"); typ
          | Some _ ->
             typ
          end
       | Some mem, false ->
          (* Printf.printf "[check_expr] Checking validity of %s\n%!" mem; *)
          do_valid_check info mem typ
     end
  | Ternary {cond=cond; tru=tru_expr; fls=fls_expr} ->
     ignore (check_expr verbose_flag prog ctx all [] cond typ);
     let tru_typ, fls_typ = partition_typ_expr typ cond in
     let tru_typ' =
       if Type.contradiction tru_typ then
         (warn_uninhabited info ~msg:"in true branch"; tru_typ)
       else
         check_expr verbose_flag prog ctx all [] tru_expr tru_typ 
     in
     let fls_typ' =
       if Type.contradiction fls_typ then
         (warn_uninhabited info ~msg:"in false branch"; fls_typ)
       else
         check_expr verbose_flag prog ctx all [] fls_expr fls_typ
     in

     Type.union tru_typ' fls_typ'
     
  | FunctionCall {func=f; type_args=_; args=args} ->
     check_args verbose_flag prog ctx all valids args typ
     |> check_dispatch `Expr verbose_flag ~act prog ctx all [] info f
     
  | NamelessInstantiation {typ=_; args=args} ->
     check_args verbose_flag prog ctx all valids args typ
  | Mask {expr=e; mask=m} ->
     typ
     |> check_expr verbose_flag prog ctx all valids m ~act:act
     |> check_expr verbose_flag prog ctx all valids e ~act:act
  | Range {lo=lo; hi=hi} ->
     typ
     |> check_expr verbose_flag prog ctx all valids lo ~act:act
     |> check_expr verbose_flag prog ctx all valids hi ~act:act
    
and check_parser_expr (verbose_flag : bool ref) prog ctx all ?act:(act="") (expr:Expression.t) (typ : Type.t) : Type.t =
  check_expr verbose_flag prog ctx all [] ~act:act expr typ

and check_control_expr (verbose_flag : bool ref) prog ctx all valids ?act:(act="") (expr:Expression.t) (typ : Type.t) : Type.t =
  check_expr verbose_flag prog ctx all valids ~act:act expr typ
  
and check_parser_match (verbose_flag : bool ref) prog ctx all (m : Match.t) typ : Type.t =
  match m with
  | (_, Match.Expression e) ->
     check_parser_expr verbose_flag prog ctx all e.expr typ
  | _ -> typ
       
and check_parser_matches (verbose_flag : bool ref) (prog : program) ctx all (matches : Match.t list) typ : Type.t =
  List.fold_left matches
    ~init:Type.empty
    ~f:(fun acc m -> check_parser_match verbose_flag prog ctx all m typ |> Type.union acc)
  
  
and check_parser_case (verbose_flag : bool ref) (prog : program) ctx all (penv : string option * (int * int) HMap.t) (case:Parser.case) typ : Type.t option =
  let (_,c) = case in
  let typ = check_parser_matches verbose_flag prog ctx all c.matches typ in
  if snd c.next = "accept" then
    Some typ
  else if snd c.next = "reject" then
    Some Type.empty
  else
    let (_, next_hop) =  lookup_parser_state prog (snd (Declaration.name ctx)) (snd c.next) in
    check_parser_state verbose_flag prog ctx all penv next_hop typ 
    
    
and check_parser_statements (verbose_flag : bool ref) (prog : program) ctx (all_hdrs : HSet.t) (penv : string option * (int * int) HMap.t) stmts typ : Type.t option =
  let open Option in
  List.fold_left stmts
    ~init:(Some (penv, typ))
    ~f:(fun acc_opt stmt ->
        acc_opt >>= fun (penv', typ') -> 
        check_parser_stmt verbose_flag prog ctx all_hdrs penv' stmt typ')
  >>= fun (_, typ) -> Some typ


  
and check_parser_exprs (verbose_flag : bool ref) prog ctx all exprs typ =
  List.fold_left exprs ~init:typ
    ~f:(fun typ expr -> check_parser_expr (verbose_flag) prog ctx all expr typ)

and check_cases (verbose_flag : bool ref) prog ctx all (penv : string option * (int * int) HMap.t) cases typ =
  (* Printf.printf "Checking %d cases \n%!" (List.length cases); *)
  List.fold_left cases
    ~init:(Type.empty)
    ~f:(fun acc case ->
        match check_parser_case verbose_flag prog ctx all penv case typ with
        | None -> acc
        | Some typ' -> Type.union acc typ'
    )
  
and check_transition (verbose_flag : bool ref) prog ctx (all : HSet.t) (penv : string option * (int * int) HMap.t) trans typ : Type.t option =
  begin
    (* Format.printf "Checking Transition at %s\n at type:\n\t" (Petr4.Info.to_string (fst trans));
     * Type.format Format.std_formatter typ;
     * Format.printf "@]%!\n";
     * Printf.printf "\n"; *)

    let open Parser in
    match trans with
    | (_, Direct {next=(_,n)}) -> 
       if n = "accept" then
         Some typ
       else if n = "reject" then
         Some Type.empty
       else
         begin 
           let (_, next_hop) = lookup_parser_state prog (snd (Declaration.name ctx)) n in
           check_parser_state verbose_flag prog ctx all penv next_hop typ
         end
    | (_, Select {exprs=es; cases=cs}) ->
      Some (typ
            |> check_parser_exprs verbose_flag prog ctx all es
            |> check_cases verbose_flag prog ctx all penv cs)
      
  end
  
and check_parser_state (verbose_flag : bool ref) (prog : program) (ctx : Declaration.t) (all_hdrs : HSet.t) (penv : 'a option * (int * int) HMap.t) (state : Parser.state) typ : Type.t option =
  let open Parser in
  let open Option in
  let (_, s) = state in
  (* Format.printf "Checking Parser State at %s\n at type:\n\t" (Petr4.Info.to_string (fst state));
   * Type.format Format.std_formatter typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n"; *)

  check_parser_statements verbose_flag prog ctx all_hdrs penv s.statements typ
  >>= check_transition verbose_flag prog ctx all_hdrs penv s.transition

  
  
and check_block (verbose_flag : bool ref) prog ctx (all : HSet.t) (valids : string list) (block : Block.t) ?act:(act="") typ : Type.t =
  let open Block in 
  let (_, b) : Block.t = block in
  List.fold_left b.statements
    ~init:typ
    ~f:(fun typ' stmt ->
      check_control_stmt verbose_flag prog ctx all valids stmt typ' ~act
    )

and check_switch_case verbose_flag prog (ctx : Declaration.t) (all : HSet.t) (valids : string list) (c : Statement.switch_case) ?act:(act="") typ =
  match c with
  | (_, FallThrough _) ->
     typ
  | (_, Action {label=_; code=block}) ->
     check_block verbose_flag prog ctx all valids block ~act typ
    
and check_switch_cases (verbose_flag : bool ref) prog (ctx : Declaration.t) (all : HSet.t) (valids : string list) (cs : Statement.switch_case list) ?act:(act="") typ : Type.t =
  List.fold_left cs ~init:Type.empty (**should be typ? *)
    ~f:(fun t c -> check_switch_case verbose_flag prog ctx all valids c typ ~act |> Type.union t)



and check_conditional_stmt (verbose_flag : bool ref) prog (ctx : Declaration.t) all (valids : string list) cond tru_ctrl fls_opt ?act:(act="") typ  =
  (* Format.printf "Checking Conditional at %s\n at type:\n\t" (Petr4.Info.to_string (fst cond));
   * Type.format Format.std_formatter typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n"; *)
  ignore (check_expr verbose_flag prog ctx all [] cond typ);
  let tru_typ, fls_typ = partition_typ_expr typ cond in
  (* Format.printf "The true branch is checked in type:\n\t";
   * Type.format Format.std_formatter tru_typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n";
   * Format.printf "The false branch is checked in type:\n\t";
   * Type.format Format.std_formatter fls_typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n"; *)
  let tru_typ' =
    if Type.contradiction tru_typ then
      (warn_uninhabited (fst cond) ~msg:"in true branch"; tru_typ)
    else
      check_control_stmt verbose_flag prog ctx all valids tru_ctrl tru_typ ~act
  in  
  let fls_typ' =
    match fls_opt with
    | None -> typ
    | Some fls_ctrl ->
       if Type.contradiction fls_typ then
         (warn_uninhabited (fst cond) ~msg:"in false branch"; fls_typ)
       else
         check_control_stmt verbose_flag prog ctx all valids fls_ctrl fls_typ ~act
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
  | (_, ExpressionMember {expr=(_,expr); name=name}) ->
     if snd name = "isValid"
     then
       true, fst (acc_members ~name:false expr)
     else
       false, None
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
  | (_, FunctionCall {func=_; type_args=[]; args=[]}) ->
     (* Printf.printf "  FUNCTION CALL\n"; *)
     begin
       match is_validity_expr expr with
       | (true, Some hdrname) ->
          Type.(restrict typ hdrname, neg_restrict typ hdrname)
       | (true, None) ->
          failwith "Error :: Could not extract header for isValid() call"
       | (false, _) ->
          (* Printf.printf "--- Couldn't find the Validity Expression---"; *)
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
               let (_, hdrstr_opt) = is_validity_expr (snd k).key in
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
  | (_, BitStringAccess {bits;
                            lo=(_, Int(_, intlo));
                            hi=(_, Int(_, inthi))}) ->
     header_inst_of_expr bits >>= fun bits_name ->
     Some (bits_name ^ "["
           ^ Bigint.to_string intlo.value ^ ":" ^
             Bigint.to_string inthi.value ^ "]")

  | (info, List _) -> error_msg "List" info
  | (info,_) -> error_msg "??" info

and check_table_key all valids typ (key : Table.key) =
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
             assert_valid info hdrstr
         end
       else ()

and check_table_action verbose_flag prog ctx all valids typ (act : Table.action_ref) =
  let open Table in
  let str = snd ((snd act).name) in
  (* let () = Printf.printf "Checking %s with valids: " str;
   *          List.iter valids ~f:(Printf.printf "%s ");
   *          Printf.printf "\n%!"
   * in *)
  let action_body = lookup_action_function prog ctx str in
  match action_body with
  | Some (_, Action a) ->  (str, check_block verbose_flag prog ctx all valids a.body typ ~act:str)
  | None -> failwith ("Error :: Could not find action "
                      ^ str ^ " in control "
                      ^ snd (Declaration.name ctx)
                      ^ " at " ^ (Petr4.Info.to_string (fst act)))
  | _ -> failwith "Error Expected Action as result of [lookup_action_function]"
  
and check_table_actions verbose_flag prog ctx all valids typ (actions : Table.action_ref list) =
  List.fold_left actions ~init:String.Map.empty
    ~f:(fun acc act ->
      let str, typ = check_table_action verbose_flag prog ctx all valids typ act in
      String.Map.add_exn acc ~key:str ~data:typ
    )

and check_matches (verbose_flag : bool ref)prog ctx all (typ : Type.t) matches =
  List.fold_left matches ~init:typ
    ~f:(fun typ' (_, mexpr) ->
      let open Match in
      match mexpr with
      | Expression {expr=expr} ->
         check_expr verbose_flag prog ctx all [] expr typ'
      | Default | DontCare ->
         typ'
    )
  
and check_entries (verbose_flag : bool ref) prog ctx all valids typ entries =
  List.iter entries
    ~f:(fun entry ->
      let open Table in
      match entry with
      | (_, {annotations=_; matches=matches; action = action} ) ->
         let open Declaration in
         let (_,act_name) = (snd action).name in
         match lookup_action_function prog ctx act_name with
         | None -> failwith ("ERROR :: Could not find " ^ act_name ^ " in context " ^ snd (name ctx))
         | Some (_,Action a) ->
            ignore(
                check_matches verbose_flag prog ctx all typ matches
                |> check_block verbose_flag prog ctx all valids a.body
              )
         | _ -> failwith "ERROR :: Expected [lookup_action_function] to return a function declaration"
    ) ; typ

and find_and_check_custom (verbose_flag : bool ref) prog ctx all customs custom_name typ =
  let default_action =
    List.fold customs ~init:None
      ~f:(fun acc prop ->
        let open Table in
        match acc, prop with
        | Some _,_ -> acc
        | None, Custom c->
           if snd c.name = custom_name then
             Some c.value
           else acc
        | _,_ -> failwith "Error :: expected custom, got some other property variant"
      )
  in
  match default_action with
  | None -> typ
  | Some act_exp ->
     check_expr verbose_flag prog ctx all [] act_exp typ

and check_table (_ : Petr4.Info.t) (verbose_flag : bool ref) prog ctx all typ tbl =
  let (valids,all_keys), actions, _(*entries*), customs = (* TODO :: Figure out customs *)
    unpack_table tbl in
  List.iter all_keys ~f:(check_table_key all valids typ);
  (* Printf.printf "valids : ";  List.iter valids ~f:(fun f -> Printf.printf "%s " f); Printf.printf "\n%!"; *)
  let acts_typ_map = check_table_actions verbose_flag prog ctx all valids typ actions in
  let def_typ = 
    find_and_check_custom verbose_flag prog ctx all customs "default_action" typ
  in
  (acts_typ_map, def_typ)


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


and check_action_run_case (verbose_flag : bool ref) prog ctx all acts_typ_map def_typ case =
  let open Statement in
  match case with
  | (info,FallThrough _) ->
     failwith ("Error :: all cases must be explicit " ^ Petr4.Info.to_string info)
  | (_, Action {label; code}) ->
     match label with
     | (_, Default) ->
        check_block verbose_flag prog ctx all [] code def_typ
     | (_, Name (_, name)) -> 
        Map.find_exn acts_typ_map name
        |> check_block verbose_flag prog ctx all [] code
       
and check_action_run_cases verbose_flag prog ctx all acts_typ_map def_typ cases =
  List.fold_left cases ~init:Type.epsilon ~f:(fun acc_typ case ->
      check_action_run_case verbose_flag prog ctx all acts_typ_map def_typ case
      |> Type.union acc_typ
    )
       
and check_action_run (verbose_flag : bool ref) prog ctx all tbl_to_apply cases typ : Type.t =
  let open Expression in
  match tbl_to_apply with
  | (_, Name (name_info,tbl_name)) ->
     begin
     match lookup_table prog ctx tbl_name with
     | None -> failwith ("Error :: Could not find table [" ^ tbl_name ^ "], invoked from " ^ Petr4.Info.to_string name_info)
     | Some tbl_props ->
        let acts_typ_map, def_typ = check_table name_info verbose_flag  prog ctx all typ tbl_props in
        check_action_run_cases verbose_flag prog ctx all acts_typ_map def_typ cases
        |> Type.union def_typ
     end
  | (tbl_call_info,_) -> failwith ("Error :: Don't know which table to call at " ^ Petr4.Info.to_string tbl_call_info )

and check_dispatch ?act:(act="") stmt_or_expr verbose_flag prog ctx all valids info func typ : Type.t =
  let open Expression in
  let casestr = match stmt_or_expr with | `Stmt -> "statement" | `Expr -> "expression" | _ -> "? ???? ? ? ?" in
  match func with
  | (_, ExpressionMember {expr=(expr_info,expr); name=mname}) ->
     begin
       match stmt_or_expr, snd mname with
       | `Stmt, "apply" ->
          begin
            match expr with
            | Name object_name ->
               begin
                 match lookup_table prog ctx (snd object_name) with
                 | None -> (* Its not a table.. is it a locally defined control?*)
                    let open Declaration in
                    begin
                      match lookup_control_instance prog ctx (snd object_name) with
                      | ((_, Control c) as ctrl_ctx)  ->
                         check_block verbose_flag prog ctrl_ctx all valids c.apply typ ~act
                      | _ -> failwith "ERROR :: expected control from [lookup_control_instance]"
                    end
                 | Some table ->
                    (* let () = Printf.printf "Checking table %s\n%!" (snd object_name) in *)
                    let acts_typ_map, def_typ = check_table info verbose_flag prog ctx all typ table  in
                    (* Type.format Format.std_formatter ent_typ;
                     * Format.printf "@]%!\n";
                     * Printf.printf "\n"; *)
                    Type.(union (typ_of_typ_map acts_typ_map) def_typ)
               end
            | _ -> failwith "TODO APPLYING SOMETHING OTHER THAN A TABLE OR CONTROL"
          end
       | `Stmt, "setValid" ->
          begin
            match fst (acc_members ~name:false expr) with
            | None ->
               failwith "Tried to setValid, but couldn't find a header to envalidate"
            | Some hdrstr ->
               Type.(add typ hdrstr)
              
          end
       | `Stmt, "setInvalid" ->
          begin
            match fst (acc_members expr) with
            | None -> failwith "Tried to setInvalid, but couldn't find a header to invalidate"
            | Some hdrstr -> Type.(remove typ hdrstr)
          end
       | _, "emit" | _,"count" | _,"execute_meter" | _,"read" | _,"lookahead" ->
          (* let mkblue str = ANSITerminal.sprintf [ANSITerminal.blue] str in *)
          (* Printf.eprintf "%s, %s : unknown string %s\n"
           *   (Petr4.Info.to_string info)
           *   (mkblue "warning")
           *   (mkblue "\"%s\"" (snd mname)); *)
          typ
       | `Stmt, "push_front" | `Stmt, "push_back" ->
          begin
            match fst(acc_members ~name:false expr) with
            | None -> failwith ("Error :: Tried to [" ^ snd mname ^ "], but could not figure out what you wanted to push at" ^ Petr4.Info.to_string expr_info)
            | Some mem ->
               let idx_to_add = (find_available_index ~start:0 prog all typ mem) |> Option.value ~default:0 in
               (* TODO ::  FIND ALL AND INCREMENT EACH *)
               mem ^ "[" ^ Int.to_string idx_to_add ^ "]" |> Type.add typ
               
          end
       | `Expr, "isValid" -> typ
       | _, action ->
          begin
          match lookup_action_function prog ctx action with
                   | Some (_, Action a) ->
                      check_block verbose_flag prog ctx all valids a.body ~act typ
                   | None ->
                      failwith ("ERROR :: Could not find " ^ casestr ^" action " ^ action
                                ^ " at " ^ (Petr4.Info.to_string info))
                   | _ ->
                      failwith "ERROR :: expected action from [lookup_action_function]"
          end
     end
  | (_, Name n) ->
     (* if snd name *) 
     let open Declaration in
     begin
       match lookup_action_function prog ctx (snd n) with
       | Some (_,Action a) -> check_block verbose_flag prog ctx all valids a.body typ
       | Some (info,_) -> failwith ("ERROR :: Expected to find Action [" ^ snd n ^ "], but it was something else at " ^ Petr4.Info.to_string info )
       | None -> 
          Printf.printf "WARNING:: Unknown name [%s] when checking control statement at %s\n%!" (snd n) (Petr4.Info.to_string info);
          typ
     end
  | _ -> failwith ("ERROR : method call must be to a member or a name at " ^ Petr4.Info.to_string info)

   
  
       
and check_control_stmt (verbose_flag : bool ref) ?act:(act="") prog ctx all valids (stmt : Statement.t) typ : Type.t=
  let open Statement in
  let (info, s) = stmt in
  let () = if !verbose_flag then Printf.printf "%s : size = %d\n%!" (Petr4.Info.to_string info) (Type.size typ) else () in
  (* Format.printf "Checking Control Statement at %s\n at type:\n\t" (Petr4.Info.to_string (fst stmt));
   * Type.format Format.std_formatter typ;
   * Format.printf "@]%!\n";
   * Printf.printf "\n"; *)
  match s with
  | MethodCall m ->
     begin match snd m.func with
     | Name (_, "update_checksum") -> typ
     | _ -> 
        check_args verbose_flag prog ctx all valids m.args typ
        |> check_dispatch `Stmt verbose_flag prog ctx all valids info m.func ~act
     end
  | Assignment a ->
     typ
     |> check_control_expr verbose_flag prog ctx all valids a.rhs ~act
     |> check_control_expr verbose_flag prog ctx all valids a.lhs ~act
  | DirectApplication {typ=cp_typ; args=args} ->
     let typ = check_args verbose_flag prog ctx all valids args typ in
     let lookfor typestr =
       let control = lookup_control_instance prog ctx typestr in
       check_control verbose_flag prog all control typ
     in
     begin
       match cp_typ with
       | (_, TopLevelType (_, typestr) ) 
         | (_, TypeName (_, typestr) ) -> lookfor typestr
       | (_, _) -> failwith "Dont know how to apply that type"
     end
     
  | Conditional {cond=cond; tru=tru_ctrl; fls=fls_opt } ->
     check_conditional_stmt verbose_flag prog ctx all valids cond tru_ctrl fls_opt typ ~act
  | BlockStatement {block=b} ->
     check_block verbose_flag prog ctx all valids b typ ~act
  | Return {expr=None} ->
     typ
  | Return {expr=(Some e)} ->
     check_control_expr verbose_flag prog ctx all valids e typ ~act
  | Switch {expr=e; cases=cs} ->
     begin
     match get_action_run_table_name e with
     | Some tbl_to_apply ->
        check_action_run verbose_flag prog ctx all tbl_to_apply cs typ
     | None -> 
        typ
        |> check_control_expr verbose_flag prog ctx all valids e ~act
        |> check_switch_cases verbose_flag prog ctx all valids cs ~act
     end    
  | DeclarationStatement _ ->
     failwith ("Error :: unsupported declaration control statement at " ^ Petr4.Info.to_string info)
  | Exit -> typ
  | EmptyStatement -> typ
                    

and check_control (verbose_flag : bool ref) prog all (ctrl : Declaration.t) typ : Type.t =
  let open Declaration in
  match ctrl with 
  | (_, Control c) -> check_block verbose_flag prog ctrl all [] c.apply typ
  | _ -> failwith ("Expected Control, got " ^ snd (name ctrl) ^ " which is not a control declaration")
       


and get_header_type_name prsr_ctx : string =
  let open Declaration in
  let open Parameter in
  match prsr_ctx with
  | (_, Parser p) ->
     begin
     match p.params with
     | _::(_,hdrs)::_ ->
        begin
          match hdrs.typ with
          | (_, TypeName (_, headers)) ->
             headers
          | _ ->
             failwith "Error : could not extract name for header type" 
        end
     | _ -> failwith ("Error :: expecting a V1Model parser, only got " ^ Int.to_string (List.length p.params) ^ " parameters")
     end
  | _ -> failwith "Error :: Expecting parser as argument to [get_header_type_name]"



and check_pipelines (verbose_flag : bool ref) prog all pipeline_names typ : Type.t =
  List.fold_left pipeline_names
    ~init:typ
    ~f:(fun typ name ->
        Printf.printf ">>>>>>checking stage %s\n%!" name;
        let stage = lookup_control_state prog name in
        (* Printf.printf "Checking %s with type of size %d\n%!" name (Type.size typ); *)
        (* Type.format Format.std_formatter typ;
           * Format.printf "@]%!\n"; Printf.printf "\n"; *)
        let outtyp = check_control verbose_flag prog all stage typ in
        Printf.printf "<<<<<<<< Checked %s!\n%!" name;
        outtyp
      )
       
and check_prog (prog : program) (verbose_flag : bool ref) : Type.t  =
  (*Lookup parser name, lookup control name(s) and check them in
     sequence, according to package named "main"*)
  let penv = parser_env prog in
  let (parser_name, pipeline_names) = lookup_package prog "main" in
  let (prsr_ctx, start_state) = lookup_parser_state prog parser_name "start" in
  Printf.printf "Analyzing %d pipeline stages\n%!" (List.length pipeline_names + 1);
  Printf.printf ">>>>>>Checking %s\n%!" parser_name;
  let all = all_insts prog (get_header_type_name prsr_ctx) in
  match check_parser_state verbose_flag prog prsr_ctx all penv start_state Type.epsilon with
  | None -> failwith "Parser may not terminate"
  | Some typ -> check_pipelines verbose_flag prog all pipeline_names typ

