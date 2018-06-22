open Batteries
open Semant
open Plain
open Pseudocode.Plain

let rec scan db va =
  if not (Database.has_proc db va) then begin
    let proc = Build_cfg.build_cfg db va in
    Database.set_proc db va proc;
    let is_leaf = ref true in
    let cfg = proc.Database.inst_cfg in
    let n = Array.length cfg.node in
    for i=0 to n-1 do
      cfg.node.(i).stmts |> List.iter begin fun inst ->
        match inst.Inst.operation with
        | I_CALL ->
          is_leaf := false;
          begin match List.hd inst.Inst.operands with
            | O_imm (dst, _) -> scan db dst
            | _ -> ()
          end
        | _ -> ()
      end
    done;
    if !is_leaf then begin
      Printf.printf "leaf function: %nx\n" va
    end
  end

let find_stack_ref db va =
  let module S = Set.Nativeint in
  let proc = Database.get_proc db va in
  let set = ref S.empty in
  let rec visit_addr_expr (ep, _ as e) =
    visit_expr e;
    match ep with
    | E_primn (Pn_add, [E_var (Var.Global R_ESP), _; E_lit bv, _]) ->
      set := S.add (Bitvec.to_nativeint bv) !set
    | _ -> ()
  and visit_expr (ep, _) =
    match ep with
    | E_lit _ -> ()
    | E_var _ -> ()
    | E_prim1 (_, e) -> visit_expr e
    | E_prim2 (_, e1, e2) -> visit_expr e1; visit_expr e2
    | E_prim3 (_, e1, e2, e3) -> visit_expr e1; visit_expr e2; visit_expr e3
    | E_primn (_, es) -> List.iter visit_expr es
    | E_load (_, _, off) -> visit_addr_expr off
    | E_nondet _ -> ()
    | E_extend (_, e, _) -> visit_expr e
    | E_shrink (e, _) -> visit_expr e
  in
  let rec visit = function
    | P_set (lv, e) ->
      begin match lv with
        | L_var _ -> ()
        | L_mem (_, off, _) -> visit_addr_expr off
      end;
      visit_expr e
    | P_goto e -> visit_expr e
    | P_if (cond, body) -> visit_expr cond; List.iter visit body
    | P_if_else (cond, body1, body2) ->
      visit_expr cond; List.iter visit body1; List.iter visit body2
    | P_do_while (body, cond) ->
      List.iter visit body; visit_expr cond
    | _ -> ()
  in
  proc.il |> List.iter visit;
  !set
