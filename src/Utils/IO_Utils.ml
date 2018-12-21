let harness_path = "harness.js"

(* Create folder safely *)
let safe_mkdir path = 
  if (not (Sys.file_exists path)) then 
    Unix.mkdir path 0o777

(* Load file from string *)
let load_file f : string =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

(* Save string to file *)
let save_file path data =
  let oc = open_out path in
    output_string oc data;
    close_out oc

(* Load a JavaScript file *)
let load_js_file path =
  let sh = if (!CCommon.js2jsil_harnessing)
    then load_file harness_path
    else "" in
  let sf = load_file path in
    sh ^ sf