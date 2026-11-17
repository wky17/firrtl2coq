From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths.

Set Implicit Arguments.
Unset Strict Implicit.

(* A cycle API for the explicit-width LoFIRRTL subset.  The circuit identifier
   names its top module.  Port lists on instances correspond, in order, to the
   referenced module's ports.  Instance paths, not module-local identifiers,
   index persistent state, so repeated nested instances do not share storage.

   Each input sample denotes a whole rising-edge cycle: all Clock inputs must
   be one.  Signals in current_values are evaluated BEFORE that edge;
   next_registers/next_memories/next_reads are committed at the NEXT sample.
   No additional evaluation with guessed future inputs is performed.

   Initialization forces each register's declared reset value (or zero for
   NRst), and initializes memories and synchronous read outputs to zero.
   Reset conditions and values must depend only on module inputs/constants.  The first
   sample supplies reset-time data inputs; an empty trace uses zero data inputs.

   None reports invalid inputs or unsupported circuits, rather than silently
   ignoring statements. Supported memories have read latency 0/1, write latency
   1 and old read-under-write. External modules, stop/when statements, implicit
   widths, recursive instances, combinational cycles, duplicate identifiers,
   multiple drivers/writers to one address and invalid accesses are rejected.
   This is NOT a claim of complete FIRRTL language support. *)
Module LoCircuit.
Module L := LoFirrtl.
Arguments data {var} _.
Arguments addr {var} _.
Arguments en {var} _.
Arguments clk {var} _.
Arguments data0 {var} _.
Arguments addr0 {var} _.
Arguments en0 {var} _.
Arguments clk0 {var} _.
Arguments mask {var} _.
Arguments mid {var} _.
Arguments data_type {var} _.
Arguments depth {var} _.
Arguments reader {var} _.
Arguments writer {var} _.
Arguments read_latency {var} _.
Arguments write_latency {var} _.
Arguments read_write {var} _.
Arguments rid {var} _.
Arguments type {var} _.
Arguments clock {var} _.
Arguments reset {var} _.
Arguments iid {var} _.
Arguments imid {var} _.
Arguments iports {var} _.
Definition port := fport VarOrder.T.
Definition stmt := fstmt VarOrder.T.
Definition modul := fmodule VarOrder.T.
Definition circuit := fcircuit VarOrder.T.
Definition sample := seq (VarOrder.T * bits).
Definition path := seq VarOrder.T.

Record module_state := ModuleState {
  current_values : Store.t;
  current_memories : L.mapmem;
  next_registers : Store.t;
  next_memories : L.mapmem;
  next_reads : Store.t
}.
Definition circuit_state := seq (path * module_state).
Record execution := Execution {
  final_state : circuit_state;
  cycles_executed : nat
}.

Fixpoint lookup {A : Type} (key : VarOrder.T) (xs : seq (VarOrder.T * A)) :=
  match xs with
  | [::] => None
  | (k,v)::tl => if key == k then Some v else lookup key tl
  end.
Fixpoint state_at (p : path) (xs : circuit_state) :=
  match xs with
  | [::] => None
  | (q,v)::tl => if p == q then Some v else state_at p tl
  end.
Definition module_id (m : modul) := match m with FInmod v _ _ | FExmod v _ _ => v end.
Fixpoint find_module (v : VarOrder.T) (ms : seq modul) :=
  match ms with [::] => None | m::tl => if module_id m == v then Some m else find_module v tl end.
Definition port_id (p : port) := match p with Finput v _ | Foutput v _ => v end.
Definition port_type (p : port) := match p with Finput _ t | Foutput _ t => t end.
Definition is_input (p : port) := match p with Finput _ _ => true | _ => false end.
Definition explicit (t : fgtyp) := match t with
  | Fuint w | Fsint w => 0 < w | Fclock | Fasyncreset => true | _ => false end.
Definition fit (t : fgtyp) (v : bits) : bits :=
  let w := sizeof_fgtyp t in
  match t with Fsint _ => take w (sext (w - size v) v)
             | _ => take w (zext (w - size v) v) end.
Definition zeros_of t := zeros (sizeof_fgtyp t).
Definition input_ok (p : port) (xs : sample) :=
  match lookup (port_id p) xs with
  | Some v => (size v == sizeof_fgtyp (port_type p)) &&
      match port_type p with Fclock => v == [::true] | _ => true end
  | None => false end.
Definition valid_sample ps xs :=
  let ins := filter is_input ps in
  uniq (map fst xs) && (size xs == size ins) && all (fun p => input_ok p xs) ins.
Definition zero_sample ps : sample :=
  map (fun p => (port_id p, match port_type p with Fclock => [::true]
                               | t => zeros_of t end)) (filter is_input ps).
Definition input_store xs := List.fold_left (fun s kv => Store.upd kv.1 kv.2 s) xs Store.empty.
Fixpoint refs (e : fexpr VarOrder.T) : seq VarOrder.T :=
  match e with
  | Econst _ _ => [::] | Eref v => [::v]
  | Ecast _ e | Eprim_unop _ e => refs e
  | Eprim_binop _ a b | Evalidif a b => refs a ++ refs b
  | Emux a b c => refs a ++ refs b ++ refs c end.
Definition ready e (known : seq VarOrder.T) := all (fun v => v \in known) (refs e).
Definition value e s te := (L.eval_fexpr e Store.empty s te [::] [::]
  (TE.empty _) (TE.empty _) (TE.empty _)).2.
Definition get_memory (v : VarOrder.T) (mm : L.mapmem) : L.memory_map :=
  match TE.find v mm with Some mem => mem | None => fun _ => [::] end.
Definition empty_state := ModuleState Store.empty (TE.empty _) Store.empty (TE.empty _) Store.empty.
Definition read_ids (m : fmem VarOrder.T) := map data (reader m).
Definition declared (st : stmt) : seq VarOrder.T := match st with
  | Swire v _ | Snode v _ => [::v] | Sreg r => [::rid r]
  | Smem m => [::mid m] ++ flatten (map (fun p => [::addr p; data p; en p; clk p]) (reader m)) ++
      flatten (map (fun p => [::addr0 p; data0 p; en0 p; clk0 p; mask p]) (writer m))
  | Sinst i => [::iid i] ++ map port_id (iports i) | _ => [::] end.
Definition supported (st : stmt) := match st with
  | Sskip | Snode _ _ | Sfcnct _ _ | Sinvalid _ | Sinst _ => true
  | Swire _ t => explicit t | Sreg r => explicit (type r)
  | Smem m => explicit (data_type m) && (0 < depth m) &&
      (read_latency m <= 1) && (write_latency m == 1) &&
      match read_write m with old => true | _ => false end
  | _ => false end.
Definition drivers (st : stmt) := match st with
  | Snode v _ | Sfcnct v _ | Sinvalid v => [::v]
  | Smem m => read_ids m
  | Sinst i => map port_id (filter (fun p => ~~ is_input p) (iports i))
  | _ => [::] end.
Definition reg_ids (ss : seq stmt) := flatten (map (fun st => match st with Sreg r => [::rid r] | _ => [::] end) ss).
Definition type_env ps ss := List.fold_left (fun te st =>
  match st with
  | Sfcnct _ _ | Snode _ _ => te
  | Smem m =>
      let te' := L.upd_typenv_fstmt st te Store.empty in
      let addr_type :=  Fuint (Nat.max 1 (Nat.log2_up (depth m))) in
      let te'' := List.fold_left (fun t p => TE.add (addr p) addr_type t) (reader m) te' in
      List.fold_left (fun t p => TE.add (addr0 p) addr_type t) (writer m) te''
  | _ => L.upd_typenv_fstmt st te Store.empty end)
  ss (L.upd_typenv_fports ps (TE.empty _)).

Fixpoint initialize_regs ss initial te s rs : option (Store.t * Store.t) :=
  match ss with
  | [::] => Some (s, rs)
  | Sreg r :: tl =>
      let ov := match initial with
      | Some previous =>
          let held := Store.acc (rid r) (next_registers previous) in
          match reset r with
          | NRst => Some held
          | Rst cond e =>
              if ready cond (map fst (TE.elements te)) && ready e (map fst (TE.elements te)) then
                match L.type_of_fexpr cond te with
                | Fasyncreset => Some (if is_zero (value cond s te) then held else fit (type r) (value e s te))
                | Fuint 1 => Some held
                | _ => None end
              else None end
      | None => match reset r with
          | NRst => Some (zeros_of (type r))
          | Rst cond e => if ready e (map fst (TE.elements te)) && ready cond (map fst (TE.elements te)) &&
              match L.type_of_fexpr cond te with Fuint 1 | Fasyncreset => true | _ => false end
              then Some (fit (type r) (value e s te)) else None end end in
      match ov with Some v => initialize_regs tl initial te (Store.upd (rid r) v s) (Store.upd (rid r) v rs)
                  | None => None end
  | _ :: tl => initialize_regs tl initial te s rs end.
Definition initial_memories ss : L.mapmem := List.fold_left (fun mm st =>
  match st with Smem m => TE.add (mid m) (fun _ => zeros_of (data_type m)) mm | _ => mm end) ss (TE.empty _).

(* Pending actions are executed only after all their input dependencies exist.
   Register connections are deferred to the edge phase. *)
Definition pending ss := filter (fun st => match st with
  | Sskip | Swire _ _ | Sreg _ => false
  | Sfcnct v _ | Sinvalid v => ~~ (v \in reg_ids ss)
  | _ => true end) ss.
Definition all_known (vs ks : seq VarOrder.T) := all (fun v => v \in ks) vs.
Definition read_ready (m : fmem VarOrder.T) ks := if read_latency m == 0 then
  all (fun p => all_known [::addr p; en p; clk p] ks) (reader m) else true.
Definition action_ready (st : stmt) ks := match st with
  | Snode _ e | Sfcnct _ e => ready e ks | Sinvalid _ => true
  | Smem m => read_ready m ks
  | Sinst i => all_known (map port_id (filter is_input (iports i))) ks
  | _ => false end.
Fixpoint choose_action ss ks : option (stmt * seq stmt) :=
  match ss with [::] => None | st::tl =>
    if action_ready st ks then Some (st,tl) else
      match choose_action tl ks with Some (chosen, rest) => Some (chosen,st::rest) | None => None end end.
Fixpoint bind_ports ps ips s : option sample :=
  match ps, ips with
  | [::], [::] => Some [::]
  | p::pt, i::it => if (is_input p == is_input i) && (port_type p == port_type i) then
      match bind_ports pt it s with Some xs =>
        Some (if is_input p then (port_id p,Store.acc (port_id i) s)::xs else xs)
      | None => None end else None
  | _, _ => None end.
Fixpoint copy_outputs ps ips child s :=
  match ps, ips with
  | p::pt, i::it => copy_outputs pt it child
      (if is_input p then s else Store.upd (port_id i) (Store.acc (port_id p) child) s)
  | _, _ => s end.

Fixpoint load_reads (ps : seq (freader_port VarOrder.T)) (m : fmem VarOrder.T) (oldmem : L.memory_map) (oldreads s : Store.t) : option Store.t :=
  match ps with
  | [::] => Some s
  | p::tl =>
      if read_latency m == 1 then
        load_reads tl m oldmem oldreads (Store.upd (data p)
          (let v := Store.acc (data p) oldreads in if v == [::] then zeros_of (data_type m) else v) s)
      else if Store.acc (en p) s == [::false] then
        load_reads tl m oldmem oldreads (Store.upd (data p) (zeros_of (data_type m)) s)
      else if (Store.acc (en p) s == [::true]) && (to_nat (Store.acc (addr p) s) < depth m) then
        load_reads tl m oldmem oldreads (Store.upd (data p) (oldmem (Store.acc (addr p) s)) s)
      else None end.

(* Edge calculations use the settled snapshot, never a partly updated memory. *)
Fixpoint writes (ps : seq (fwriter_port VarOrder.T)) (m : fmem VarOrder.T) (s : Store.t) (mem : L.memory_map) (used : seq bits) : option L.memory_map :=
  match ps with
  | [::] => Some mem
  | p::tl =>
      if Store.acc (clk0 p) s != [::true] then None else
      if (Store.acc (en0 p) s == [::false]) || (Store.acc (mask p) s == [::false]) then writes tl m s mem used
      else let a := Store.acc (addr0 p) s in
        if (Store.acc (en0 p) s == [::true]) && (Store.acc (mask p) s == [::true]) &&
           (to_nat a < depth m) && ~~ (a \in used) then
          writes tl m s (L.memupd a (fit (data_type m) (Store.acc (data0 p) s)) mem) (a::used)
        else None end.
Fixpoint sample_reads (ps : seq (freader_port VarOrder.T)) (m : fmem VarOrder.T) (s : Store.t) (mem : L.memory_map) (out : Store.t) : option Store.t :=
  match ps with
  | [::] => Some out
  | p::tl => if Store.acc (clk p) s != [::true] then None else
      if Store.acc (en p) s == [::false] then sample_reads tl m s mem out
      else let a := Store.acc (addr p) s in
        if (Store.acc (en p) s == [::true]) && (to_nat a < depth m) then
          sample_reads tl m s mem (Store.upd (data p) (mem a) out) else None end.
Fixpoint edge_memories ss (ks : seq VarOrder.T) s mm reads : option (L.mapmem * Store.t) :=
  match ss with [::] => Some (mm,reads) | st::tl =>
    match st with
    | Smem m => if all (fun p => all_known [::addr0 p; data0 p; en0 p; clk0 p; mask p] ks) (writer m) &&
        all (fun p => all_known [::addr p; en p; clk p] ks) (reader m) then
        let oldmem := get_memory (mid m) mm in
        match writes (writer m) m s oldmem [::], sample_reads (reader m) m s oldmem reads with
        | Some mem, Some rd => edge_memories tl ks s (TE.add (mid m) mem mm) rd
        | _, _ => None end else None
    | _ => edge_memories tl ks s mm reads end end.
Fixpoint register_drives (ss : seq stmt) (regs ks : seq VarOrder.T) s te rs : option Store.t :=
  match ss with
  | [::] => Some rs
  | Sfcnct v e :: tl => if v \in regs then
      if ready e ks then register_drives tl regs ks s te (Store.upd v (value e s te) rs) else None
      else register_drives tl regs ks s te rs
  | Sinvalid v :: tl => if v \in regs then None else register_drives tl regs ks s te rs
  | _ :: tl => register_drives tl regs ks s te rs end.
Fixpoint reset_and_fit ss ks s te rs : option Store.t :=
  match ss with
  | [::] => Some rs
  | Sreg r :: tl => if Store.acc (clock r) s != [::true] then None else
      let ov := match reset r with
      | NRst => Some (Store.acc (rid r) rs)
      | Rst cond e => if ready cond ks && ready e ks then
          Some (if is_zero (value cond s te) then Store.acc (rid r) rs else value e s te)
          else None end in
      match ov with Some v => reset_and_fit tl ks s te (Store.upd (rid r) (fit (type r) v) rs)
                  | None => None end
  | _ :: tl => reset_and_fit tl ks s te rs end.

Fixpoint eval_module (fuel : nat) (ms : seq modul) (mi : VarOrder.T)
  (p : path) (previous : circuit_state) (inputs : sample) (resetting : bool)
  : option circuit_state :=
  match fuel with
  | 0 => None
  | S fuel' => match find_module mi ms with
    | Some (FInmod _ ps ss) =>
      if all (fun p => explicit (port_type p)) ps && all supported ss &&
         uniq (map port_id ps ++ flatten (map declared ss)) &&
         uniq (flatten (map drivers ss)) && valid_sample ps inputs then
      let previous_module := if resetting then None else state_at p previous in
      let input_te := L.upd_typenv_fports (filter is_input ps) (TE.empty _) in
      let te := type_env ps ss in
      match initialize_regs ss previous_module input_te (input_store inputs) Store.empty with
      | None => None
      | Some (s0, rs0) =>
        let mm := match previous_module with Some prev => next_memories prev | None => initial_memories ss end in
        let rd := match previous_module with Some prev => next_reads prev | None => Store.empty end in
        let work := pending ss in
        let fix settle (n : nat) (todo : seq stmt) (ks : seq VarOrder.T)
          (s : Store.t) (tenv : TE.env) (children : circuit_state)
          : option (Store.t * TE.env * seq VarOrder.T * circuit_state) :=
          match todo with
          | [::] => Some (s,tenv,ks,children)
          | _ => match n with 0 => None | S n' =>
            match choose_action todo ks with
            | None => None
            | Some (st,rest) =>
              let next := match st with
              | Snode v e => let t := L.type_of_fexpr e tenv in
                  Some (Store.upd v (fit t (value e s tenv)) s, TE.add v t tenv, [::v],children)
              | Sfcnct v e => match TE.find v tenv with
                  | Some t => Some (Store.upd v (fit t (value e s tenv)) s,tenv,[::v],children)
                  | None => None end
              | Sinvalid _ => None
              | Smem m => match load_reads (reader m) m (get_memory (mid m) mm) rd s with
                  | Some s' => Some (s',tenv,read_ids m,children) | None => None end
              | Sinst i => match find_module (imid i) ms with
                  | Some (FInmod _ cps _) => match bind_ports cps (iports i) s with
                    | Some ci => match eval_module fuel' ms (imid i) (p ++ [::iid i]) previous ci resetting with
                      | Some states => match state_at (p ++ [::iid i]) states with
                        | Some child => Some (copy_outputs cps (iports i) (current_values child) s,tenv,
                            map port_id (filter (fun q => ~~ is_input q) (iports i)), states ++ children)
                        | None => None end
                      | None => None end
                    | None => None end
                  | _ => None end
              | _ => None end in
              match next with Some (s',te',known,cs) => settle n' rest (known ++ ks) s' te' cs
                            | None => None end
            end end end in
        match settle (size work) work (map fst inputs ++ reg_ids ss) s0 te [::] with
        | Some (s,tenv,ks,children) =>
          if all_known (map port_id (filter (fun q => ~~ is_input q) ps)) ks then
          if resetting then Some ((p, ModuleState s mm rs0 mm rd)::children) else
          match register_drives ss (reg_ids ss) ks s tenv rs0,
                edge_memories ss ks s mm rd with
          | Some raw_regs, Some (mm',rd') => match reset_and_fit ss ks s tenv raw_regs with
              | Some regs => Some ((p,ModuleState s mm regs mm' rd')::children)
              | None => None end
          | _, _ => None end else None
        | None => None end
      end else None
    | _ => None end
  end.

Fixpoint execute_samples ms top inputs state : option circuit_state :=
  match inputs with
  | [::] => Some state
  | x::xs => match eval_module (size ms) ms top [::] state x false with
      | Some next => execute_samples ms top xs next | None => None end end.

(* Public entry: input port -> equal-length sequence of width-correct values.
   Clocks must be one in every sample (one complete cycle per sample).
   Empty sequences return the forced-reset snapshot with zero completed cycles.
   All instance states can be retrieved using state_at [:: instance; child; ...]. *)
Definition run_circuit (c : circuit) (input_sequences : seq (VarOrder.T * seq bits))
  : option execution :=
  let '(Fcircuit top ms) := c in
  match find_module top ms with
  | Some (FInmod _ ps _) =>
    let ins := filter is_input ps in
    let n := match input_sequences with [::] => 0 | (_,xs)::_ => size xs end in
    if uniq (map module_id ms) && uniq (map fst input_sequences) &&
       (size input_sequences == size ins) &&
       all (fun p => match lookup (port_id p) input_sequences with Some xs => size xs == n | None => false end) ins then
    let samples := map (fun k => map (fun vx => (vx.1, nth [::] vx.2 k)) input_sequences) (iota 0 n) in
    if all (valid_sample ps) samples then
    let reset_inputs := head (zero_sample ps) samples in
    match eval_module (size ms) ms top [::] [::] reset_inputs true with
    | Some initial => match execute_samples ms top samples initial with
        | Some final => Some (Execution final n) | None => None end
    | None => None end else None else None
  | _ => None end.
End LoCircuit.
