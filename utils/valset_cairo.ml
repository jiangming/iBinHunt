(* XXX unknown_frac is for probabilistic density, e.g. via sampling.
   XXX ought to make surface modular; e.g. update an x11 surface.
   this should be carried within the value set, ideally supporting
   sampling unknown regions separately. no time to refactor right now.
*)
let valset_to_ps filename width height vs unknown_frac = 
  let min_line_width = 0.2 in
  let surface = 
    Cairo.image_surface_create 
      Cairo.FORMAT_ARGB32 
      ~width:width
      ~height:height 
  in
  let surface =
    Cairo_ps.surface_create_for_channel 
      (open_out filename)
      ~width_in_points:(float_of_int width)
      ~height_in_points:(float_of_int height)
  in
  let ctx = Cairo.create surface in

  let width = float_of_int width in
  let height = float_of_int height in
  let mid_height = height /. 2. in

  (* draw perimeter *)
  Cairo.set_line_width ctx min_line_width ;
  Cairo.rectangle ctx 0. 0. width height;
  Cairo.stroke ctx;

  (* Draw start point *)
(*   Cairo.set_line_width ctx mid_height ; *)
(*   Cairo.move_to ctx 0. mid_height; *)
(*   Cairo.rel_line_to ctx 1. 0.; *)
(*   Cairo.stroke ctx; *)

  (* find max x value, for scaling *)
  let max_x =
    let (_, max_x, _) = 
      List.last vs.ranges
    in
    Int64.to_float max_x
  in
  let scale_x x =
    (Int64.to_float x) /. max_x *. width
  in

  List.iter
    (fun (x0, x1, b) ->
       let line_width, opacity = 
         (match b with
          | TRUE -> 
              height, 1.
          | FALSE -> 
              min_line_width, 1.
          | UNKNOWN -> 
              unknown_frac *. height, 0.5
         ) in
       let x0, x1 = scale_x x0, scale_x x1 in
       Cairo.set_source_rgba ctx 0. 0. 0. opacity;
       Cairo.set_line_width ctx line_width ;
       Cairo.move_to ctx x0 mid_height;
       Cairo.rel_line_to ctx (max min_line_width (x1 -. x0)) 0.;
       Cairo.stroke ctx
    )
    vs.ranges;

  (* Draw end point *)
(*   Cairo.set_line_width ctx mid_height ; *)
(*   Cairo.move_to ctx (width -. 1.) mid_height; *)
(*   Cairo.rel_line_to ctx 1. 0.; *)
(*   Cairo.stroke ctx; *)

  (* Output a PNG file *)
(*   Cairo_png.surface_write_to_file surface filename *)
  Cairo.surface_flush surface;
  Cairo.surface_finish surface
;;



