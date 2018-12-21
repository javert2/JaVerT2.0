let input = ref ""
let output = ref ""

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let arguments () =
  let usage_msg="Usage: -file <path> -output <path>" in
  Arg.parse
    [
      (* input to pretty-print *)
      "-input", Arg.String(fun f -> input := f), "file to pretty-print";

      (* pretty-printed output file *)
      "-output", Arg.String(fun f -> output := f), "output file";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg;
  if (!output = "") then output := !input

let burn_to_disk (path : string) (data : string) : unit =
  let oc = open_out path in
  output_string oc data;
  close_out oc

let main () =
  arguments ();
  burn_to_disk !output (EProg.str (Parsing_Utils.parse_eprog_from_file !input))

let _ = main ()