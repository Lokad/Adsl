module Adsl.Liveness

open Adsl.Program
open Adsl.Adsl

open System.Collections.Generic




/// <summary> Returns the set of variables read at least once in an ADSL program. </summary>
let liveVariables (p: Program<'t>) : HashSet<AdslVar<'t>> = 
 
    let alive = HashSet()
    let read mv = ignore (alive.Add mv)
    
    // Recursively explore statements, identifying all variable reads
    let rec ofStmt (stmt: AdslStmt<'t>) = 
        match stmt with 
        | AdslRawEpoch    _ 
        | AdslRawLoad     _ 
        | AdslParam       _  -> ()
        | AdslVar    (w, r)  -> if alive.Contains w then read r
        | AdslAdd    (w, rs) -> if alive.Contains w then Array.iter read rs
        | AdslTup    (ws, r) -> if Array.exists alive.Contains ws then read r
        | AdslMap    (w, mr) -> if alive.Contains w then Array.iter read mr.ReadVariables
        | AdslRawMap (w, mr) -> if alive.Contains w then Array.iter read mr.Arguments
        | AdslCond      cond -> 

            let mutable anyOutput = false

            for phi in cond.Phis do 
                if alive.Contains phi.WrittenVariable then 
                    Array.iter read phi.ReadVariables
                    anyOutput <- true

            if anyOutput then 

                read cond.If

                for i = cond.IfFalse.Length - 1 downto 0 do 
                    ofStmt cond.IfFalse.[i]

                for i = cond.IfTrue.Length - 1 downto 0 do 
                    ofStmt cond.IfTrue.[i]

                for psi in cond.Psis do 
                    if Array.exists alive.Contains psi.WrittenVariables then
                        read psi.ReadVariable

        | AdslLoop      loop -> 

            for a in loop.OutArrays do 
                if alive.Contains a.Array then 
                    read a.Scalar

            for s in loop.Sums do 
                if alive.Contains s.Outer then 
                    read s.Inner

            for s in loop.State do 
                match s.OuterFinal with 
                | Some v when alive.Contains v -> 
                    read s.InnerFinal
                    // TODO: we could try to detect if 'init' is unused, but there's
                    // no clean way to represent a write-only state anyway...
                    read s.InnerInit
                | _ -> ()

            // Perform a fixpoint search on the liveness of the state variables. 
            // If a state's InnerInit is determined to be live, then repeat the 
            // pass after marking the state's InnerFinal as live as well.
            //
            // 'stateUsed' remembers if a given InnerInit was unused before a traversal,
            // to detect when the fixpoint has been reached.
            let stateUsed = loop.State |> Array.map (fun s -> alive.Contains s.InnerInit)
            let rec fixpoint () = 

                for i = loop.Statements.Length - 1 downto 0 do 
                    ofStmt loop.Statements.[i]

                let mutable repeat = false
                for i = 0 to stateUsed.Length - 1 do 
                    if not stateUsed.[i] && alive.Contains loop.State.[i].InnerInit then 
                        stateUsed.[i] <- true
                        read loop.State.[i].InnerFinal
                        repeat <- true

                if repeat then fixpoint ()

            fixpoint () 


            for s in loop.State do 
                if alive.Contains s.InnerInit then 
                    Option.iter read s.OuterInit

            for b in loop.Broadcasts do 
                if alive.Contains b.Inner then 
                    read b.Outer

            for a in loop.InArrays do 
                if alive.Contains a.Scalar then 
                    read a.Array

    Seq.iter read p.ReturnedVariables
    for i = p.Statements.Length - 1 downto 0 do 
        ofStmt p.Statements.[i]

    alive

