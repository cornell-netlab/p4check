open Core
open Petr4
open P4check

let verbose_flag = ref false


let colorize colors s = ANSITerminal.sprintf colors "%s" s
let red s = colorize [ANSITerminal.red] s
let green s = colorize [ANSITerminal.green] s
                 
let preprocess include_dirs p4file = 
  let cmd = 
    String.concat ~sep:" "
      (["cc"] @ 
       (List.map include_dirs ~f:(Printf.sprintf "-I%s") @
       ["-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file])) in 
  let in_chan = Unix.open_process_in cmd in
  let str = In_channel.input_all in_chan in 
  let _ = Unix.close_process_in in_chan in
  str
                 
let parse include_dirs p4_file verbose = 
  let () = Lexer.reset () in 
  let () = Lexer.set_filename p4_file in
  let p4_string = preprocess include_dirs p4_file in
  let lexbuf = Lexing.from_string p4_string in
  try
    let prog = Parser.p4program Lexer.lexer lexbuf in 
    if verbose then Format.eprintf "[%s] %s@\n%!" (green "Passed") p4_file;      
    `Ok prog
  with
  | err -> 
    if verbose then Format.eprintf "[%s] %s@\n%!" (red "Failed") p4_file;
    `Error (Lexer.info lexbuf, err)
   
let spec =
  let open Command.Spec in
  empty
  +> flag "-I" (listed string) ~doc:"<dir> Add directory to include search path"
  +> flag "-v" no_arg ~doc:"verbose mode, print the size of the types \
                            at each control statement"
  +> anon ("p4file" %:string)
    
let command =
  Command.basic_spec
    ~summary:"p4check: P4 static checker"
    spec
    (fun include_dirs v p4_file () ->
       verbose_flag := v;
       match parse include_dirs p4_file v with
       | `Ok prog ->
          begin
            let () = Format.set_margin 160 in 
            let () = Format.printf "@[" in
            (* let () = verbose (lazy (Format.printf ">>> Checking program: %s@\n%!" fn)) in *) 
            ignore(check_prog prog verbose_flag);
            Printf.printf "Done!\n%!"
          end
       | `Error (info, Lexer.Error s) -> 
          Format.eprintf "%s: %s@\n%!" (Info.to_string info) s
       | `Error (info, Petr4.Parser.Error) -> 
          Format.eprintf "%s: syntax error@\n%!" (Info.to_string info) 
       | `Error (info, err) -> 
          Format.eprintf "%s: %s@\n%!" (Info.to_string info) (Exn.to_string err)
    )


let () =
  Gc.(set { (get ()) with 
    minor_heap_size=33554432;
    major_heap_increment=200;
    space_overhead=100;
    max_overhead=200000;
  });
  Command.run ~version:"0.1" command

