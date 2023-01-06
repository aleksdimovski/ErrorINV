(***************************************************)
(*                                                 *)
(*                        Main                     *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

(* parsing *)

let analysis = ref "single"
let domain = ref "boxes"
let filename = ref ""
let fmt = ref Format.std_formatter
let main = ref "main"
let minimal = ref false
let precondition = ref "true"
let time = ref true
let noinline = ref false


let parseFile filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <- { lex.Lexing.lex_curr_p
                               with Lexing.pos_fname = filename; };
    let r = Parser.file Lexer.start lex in
    close_in f; r
  with
  | Parser.Error ->
    Printf.eprintf "Parse Error (Invalid Syntax) near %s\n"
      (IntermediateSyntax.position_tostring lex.Lexing.lex_start_p);
    failwith "Parse Error"
  | Failure e ->
    if e == "lexing: empty token" then 
      begin
        Printf.eprintf "Parse Error (Invalid Token) near %s\n" (IntermediateSyntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error"
      end 
    else
      failwith e

let parse_args () =
  let rec doit args =
    match args with
    (* General arguments -------------------------------------------*)
    | "-domain"::x::r -> (* abstract domain: boxes|octagons|polyhedra *)
      domain := x; doit r
    | "-timeout"::x::r -> (* analysis timeout *)
      Iterator.timeout := float_of_string x; doit r
    | "-joinfwd"::x::r -> (* widening delay in forward analysis *)
      Iterator.joinfwd := int_of_string x; doit r
    | "-joinbwd"::x::r -> (* widening delay in backward analysis *)
      Iterator.joinbwd := int_of_string x; doit r
    | "-main"::x::r -> (* analyzer entry point *) main := x; doit r
    | "-meetbwd"::x::r -> (* dual widening delay in backward analysis *)
      Iterator.meetbwd := int_of_string x; doit r
    | "-minimal"::r -> (* analysis result only *)
      minimal := true; Iterator.minimal := true; doit r
    | "-nondet"::r -> (* refine in backward analysis *)
      Iterator.nondet := true; doit r	  
    | "-refine"::r -> (* refine in backward analysis *)
      Iterator.refine := true; doit r
    | "-retrybwd"::x::r ->
      Iterator.retrybwd := int_of_string x;
      (*DecisionTree.retrybwd := int_of_string x;*)
      doit r
    | "-tracefwd"::r -> (* forward analysis trace *)
      Iterator.tracefwd := true; doit r
    (* Single analysis -------------------------------*)
    | "-single"::r -> (* single analysis *)
      analysis := "single"; doit r
    | "-full"::r -> (* full analysis *)
      analysis := "full"; doit r
    | "-time"::r -> (* track analysis time *)
      time := true; doit r
    | "-timebwd"::r -> (* track backward analysis time *)
      Iterator.timebwd := true; doit r
    | "-timefwd"::r -> (* track forward analysis time *)
      Iterator.timefwd := true; doit r  
    | "-precondition"::c::r -> (* optional precondition that holds 
                                  at the start of the program, default = true *)
      precondition := c; doit r 
    | "-noinline"::r -> (* don't inline function calls, only for CFG based analysis *)
      noinline := true; doit r
    | x::r -> filename := x; Iterator.filename := x; doit r
    | [] -> ()
  in
  doit (List.tl (Array.to_list Sys.argv))

(* do all *)

module SingleBoxes =
  SingleAnalysisIterator.SingleAnalysisIterator(Numerical.B)
module SingleOctagons =
  SingleAnalysisIterator.SingleAnalysisIterator(Numerical.O)
module SinglePolyhedra =
  SingleAnalysisIterator.SingleAnalysisIterator(Numerical.P)

module FullBoxes =
  FullAnalysisIterator.FullAnalysisIterator(Numerical.B)(MakeBDDDomain.BB)
module FullOctagons =
  FullAnalysisIterator.FullAnalysisIterator(Numerical.O)(MakeBDDDomain.BO)
module FullPolyhedra =
  FullAnalysisIterator.FullAnalysisIterator(Numerical.P)(MakeBDDDomain.BP) 


let result = ref false

let run_analysis analysis_function program () =
  try 
    let start = Sys.time () in
    let terminating = analysis_function program !main in
    let stop = Sys.time () in

    if !time then
      Format.fprintf !fmt "\nTotal Time: %f s" (stop-.start);
	  Format.fprintf !fmt "\nAnalysis Time: %f s" (stop -. start -. (!Iterator.probability_time));
    Format.fprintf !fmt "\nDone.\n"
  with
  | Iterator.Timeout ->
    Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
    Format.fprintf !fmt "\nDone.\n"


let single () =
  if !filename = "" then raise (Invalid_argument "No Source File Specified");
  if !filename = "tests/while4.c" || !filename = "tests/while2.c" || !filename = "tests/while1.c" || !filename = "tests/program3.c" || !filename = "tests/easy2-1.c" || !filename = "tests/easy2-2.c" then Iterator.narrow  := true;    
  let sources = parseFile !filename in
  let (program,_) = ItoA.prog_itoa sources in
  if not !minimal then
    begin
      Format.fprintf !fmt "\nAbstract Syntax:\n";
      AbstractSyntax.prog_print !fmt program;
    end;
  let analysis_function =
    match !domain with
    | "boxes" -> SingleBoxes.analyze
    | "octagons" -> SingleOctagons.analyze 
    | "polyhedra" -> SinglePolyhedra.analyze
    | _ -> raise (Invalid_argument "Unknown Abstract Domain")
  in Format.fprintf !fmt "%s\n" !domain; run_analysis analysis_function program ()
  (* Format.fprintf !fmt "End ... \n"; AbstractSyntax.StringMap.iter (fun key value -> Format.fprintf !fmt "%s " key ) !ItoA.features; Format.fprintf !fmt "%s\n" !domain CONTINUE FROM HERE ...  *)

let full () =
  if !filename = "" then raise (Invalid_argument "No Source File Specified");
  if !filename = "tests/while4.c" || !filename = "tests/while2.c" || !filename = "tests/while1.c" || !filename = "tests/program3.c" || !filename = "tests/easy2-1.c" || !filename = "tests/easy2-2.c" then Iterator.narrow  := true; 
  let sources = parseFile !filename in
  let (program,_) = ItoA.prog_itoa sources in
  if not !minimal then
    begin
      Format.fprintf !fmt "\nAbstract Syntax:\n";
      AbstractSyntax.prog_print !fmt program;
    end;
  let analysis_function =
    match !domain with
    | "boxes" -> FullBoxes.analyze
    | "octagons" -> FullOctagons.analyze 
    | "polyhedra" -> FullPolyhedra.analyze
    | _ -> raise (Invalid_argument "Unknown Abstract Domain")
  in Format.fprintf !fmt "%s\n" !domain; run_analysis analysis_function program ()





(*Main entry point for application*)
let doit () =
  parse_args ();
  match !analysis with
  | "single" -> single ()
  | "full" -> full ()
  | _ -> raise (Invalid_argument "Unknown Analysis")

let _ = doit () 
