module Adsl.SSASA

open Adsl.Tables
open Adsl.Program
open Adsl.Adsl
open Adsl.Liveness

open System.Collections.Generic


/// <summary> 
///     Transform a program, so that every variable is read exactly
///     once. This will perform dead code elimination on variables that
///     are not read at all, and will introduce AdslTup operations 
///     for variables that are used more than once.
/// </summary>
let toSingleAssignment (adsl: Program<'o>): Program<'n> = 

    // This algorithm traverses the program from bottom to top, keeping track
    // of all the uses of every old-variable as a list-of-fresh-variables. Every 
    // read of an old-variable adds a new-variable to the list ; every write 
    // consumes the list of new-variables to decide whether to drop the assignment, 
    // to just keep the statement, or to insert a tupling.

    // If we encounter state in loops, our naive top-bottom traversal will not know
    // which state variables are used or not ; we need full-blown liveness analysis
    // (including fixpoint search) for that. 
    let live = lazy liveVariables adsl 

    let mentos = AdslMentos<'n>()

    // For each old-variable, a list that contains, for each time this variable
    // was read, the new-variable that was created for that read.
    let reads = Array.create adsl.Mentos.Count []

    // Register a read for an old-variable, adding it to 'reads' and returning
    // a new-variable that is unique to that read. Thus it is a guarantee that
    // 'read' returns a different variable on every call (to ensure single access)
    let read (oldV: AdslVar<'o>) = 
        let newV = mentos.Fresh oldV
        reads.[oldV.Id] <- newV :: reads.[oldV.Id]
        newV
    
    let assertSingleRead (oldV : AdslVar<'t>) = reads.[oldV.Id].Head
    let trySingleRead (oldV: AdslVar<'t>) = List.tryHead reads.[oldV.Id]
    let readsOf (oldV: AdslVar<'t>) = reads.[oldV.Id]

    // Loss, gradients and metrics count as read
    let gradients = Array.map read adsl.Gradients
    let loss = read adsl.Loss
    let metrics = Array.map read adsl.Metrics
    
    // If provided with a list of more than one read, appends an 'AdslTup'
    // for those reads to the statements. Returns a variable with exactly 
    // one read in all cases.
    let addTupToEnsureSingleRead (stmts: List<_>) = function 
        | [newV] -> Some newV
        | (newV :: _) as list -> 
             let newV = mentos.Fresh newV
             stmts.Add <| AdslTup (Array.ofList list, newV)
             Some newV
        | [] -> None

    // Traverses an array of statements and returns a list of transformed 
    // statements, in reverse order.
    let rec traverseBack (stmts:AdslStmt<'o>[]) : List<AdslStmt<'n>> = 
        let newStmts = List<AdslStmt<'n>>()

        for s = stmts.Length - 1 downto 0 do 
            let stmt = stmts.[s]

            // After this loop: 
            //  - each old-variable written by the statement will have either 
            //    0 or 1 read in 'reads', never more. 
            //  - 'hasAtLeastOneRead' will be true if and only if there was 
            //    at least one old-variable written by the statement that had 
            //    at least one read in 'reads'.
            let mutable hasAtLeastOneRead = false
            for oldV in stmt.WrittenVariables do 
                match addTupToEnsureSingleRead newStmts (readsOf oldV) with 
                | None -> ()
                | Some newV -> hasAtLeastOneRead <- true
                               reads.[oldV.Id] <- [newV]

            // A statement has no side-effect beyond writing variables, 
            // so if none of the written variables are read, the entire 
            // statement can be dropped.
            if not hasAtLeastOneRead then () else
                         
            // Below, statements which write only one variable can safely 
            // expect that variable to be read exactly once.

            match stmts.[s] with 

            // Simple statements: only one variable being written-to.
            // ------------------------------------------------------

            | AdslAdd (w, rs) -> 
                newStmts.Add <| AdslAdd (assertSingleRead w, Array.map read rs)
            | AdslMap (w, m) ->
                newStmts.Add <| AdslMap (assertSingleRead w, m.Map read)
            | AdslRawEpoch w ->
                newStmts.Add <| AdslRawEpoch (assertSingleRead w)
            | AdslRawMap (w, m) -> 
                newStmts.Add <| AdslRawMap (assertSingleRead w, 
                                            { Function = m.Function
                                              Arguments = Array.map read m.Arguments })
            | AdslRawLoad (w, load) -> 
                newStmts.Add <| AdslRawLoad (assertSingleRead w, load.Force())
            | AdslParam (w, p) ->
                newStmts.Add <| AdslParam (assertSingleRead w, p)

            // Variable copy statements
            // ------------------------

            | AdslVar (w, r) -> 
                // Use the occasion to get rid of the 'AdslVar' by copying its reads to 
                // the read-variable.
                reads.[r.Id] <- assertSingleRead w :: reads.[r.Id]
            | AdslTup (ws, r) -> 
                // Rather than spend effort to filter out 'ws' and emit either an 'AdslTup'
                // or an 'AdslVar', we just copy over all reads to the 'r' variable, and 
                // let that variable generate an AdslTup on its own when it is reached
                // by the algorithm.
                reads.[r.Id] <- ws |> Array.fold (fun l w -> List.append (readsOf w) l) reads.[r.Id]

            // Complex statements 
            // ------------------

            | AdslCond cond ->

                // Start with 'phi' to accumulate any reads of the variables inside the if-true
                // and if-false blocks. A 'phi' with an output that is not read is simply discarded.
                let phi = cond.Phis |> Array.choose (fun phi ->
                    match phi with 
                    | Phi (w, rt, rf) -> trySingleRead w |> Option.map (fun w -> Phi (w, read rt, read rf))
                    | PhiT    (w, rt) -> trySingleRead w |> Option.map (fun w -> PhiT (w, read rt))
                    | PhiF    (w, rf) -> trySingleRead w |> Option.map (fun w -> PhiF (w, read rf)))

                let ifFalse = traverseBack cond.IfFalse
                let ifTrue = traverseBack cond.IfTrue

                // Traverse the 'psi', determining if it is read in the if-true, if-false, or in 
                // both blocks. 
                // If read in at most one of them, then keep the 'psi' and prepend 'AdslTup' 
                // statements to the if-true or if-false blocks as needed
                let psi = cond.Psis |> Array.choose (fun psi -> 
                    let (r, wt, wf) = 
                        match psi with 
                        | Psi (wt, wf, r) -> r, 
                                             addTupToEnsureSingleRead ifTrue (readsOf wt),
                                             addTupToEnsureSingleRead ifFalse (readsOf wf)
                        | PsiT (wt, r) -> r, addTupToEnsureSingleRead ifTrue (readsOf wt), None
                        | PsiF (wf, r) -> r, None, addTupToEnsureSingleRead ifFalse (readsOf wf)
                    match wt, wf with 
                    | None,    None    -> None
                    | Some wt, None    -> Some (PsiT (wt, read r))
                    | None,    Some wf -> Some (PsiF (wf, read r))
                    | Some wt, Some wf -> Some (Psi (wt, wf, read r)))

                ifFalse.Reverse()
                ifTrue.Reverse()

                newStmts.Add <| AdslCond {
                    If = read cond.If 
                    Phis = phi
                    Psis = psi
                    IfTrue = ifTrue.ToArray()
                    IfFalse = ifFalse.ToArray() }

            | AdslLoop loop -> 

                // Start with the outputs to determine which must be kept
                let sums = 
                    loop.Sums
                    |> Array.choose (fun s -> 
                        trySingleRead s.Outer |> Option.map (fun o -> { 
                            Outer = o 
                            Inner = read s.Inner 
                            IndexPair = s.IndexPair |> Option.map (fun p -> p.Force()) }))

                let outArrays = 
                    loop.OutArrays
                    |> Array.choose (fun a -> 
                        trySingleRead a.Array 
                        |> Option.map (fun k -> { Array = k ; Scalar = read a.Scalar }))

                let partialState =
                    loop.State
                    |> Array.where (fun s -> live.Value.Contains s.InnerInit) 
                    |> Array.map (fun s -> 
                        let outerFinal = Option.bind trySingleRead s.OuterFinal
                        let outerInit  = Option.map read s.OuterInit
                        let innerFinal = read s.InnerFinal
                        // The above must be evaluated BEFORE the traversal of the loop
                        // statements, but the 'InnerInit' must be evaluated AFTER, so 
                        // we return a function that will evaluate it. 
                        fun stmts -> { 
                            OuterFinal = outerFinal
                            OuterInit  = outerInit
                            InnerFinal = innerFinal
                            InnerInit  = addTupToEnsureSingleRead stmts (readsOf s.InnerInit)
                                         // We pretend that the variable is read at least once, 
                                         // because there's no clean way to represent write-only 
                                         // state in ADSL.
                                         |> Option.defaultWith (fun () -> read s.InnerInit) })

                let body = traverseBack loop.Statements

                // Traverse the inputs, determining if they are used in the body. If they 
                // are not, discard them. If they are, prepend 'AdslTup' as needed and
                // keep them.
                let broadcasts = 
                    loop.Broadcasts
                    |> Array.choose (fun b -> 
                        addTupToEnsureSingleRead body (readsOf b.Inner) |> Option.map (fun i -> {
                            Inner = i 
                            Outer = read b.Outer 
                            IndexPair = b.IndexPair |> Option.map (fun p -> p.Force()) }))

                let inArrays = 
                    loop.InArrays
                    |> Array.choose (fun a -> 
                        addTupToEnsureSingleRead body (readsOf a.Scalar)
                        |> Option.map (fun s -> { Array = read a.Array ; Scalar = s }))

                let state = Array.map (fun f -> f body) partialState

                body.Reverse()

                newStmts.Add <| AdslLoop {
                    Sums       = sums
                    OutArrays  = outArrays
                    Broadcasts = broadcasts
                    InArrays   = inArrays
                    DebugName  = loop.DebugName
                    State      = state
                    Statements = body.ToArray()
                    Reverse    = loop.Reverse
                    Table      = TblId<'n> loop.Table.Id }
                    
        newStmts

    let stmts = traverseBack adsl.Statements

    stmts.Reverse()

    {   Mentos = mentos
        Statements = stmts.ToArray() 
        Loss = loss
        Gradients = gradients
        Metrics = metrics 
        // We need to preserve the parameter and epoch variables in 
        // the Autodiff meta-data. These do not count as actual reads 
        // or writes : they are instead written by an appropriate 
        // statement (or not at all), for which tupling should have
        // already happened if necessary. If not read, then we create
        // a fresh variable, since we know it will be unused.
        Meta = adsl.Meta.Map (fun v -> 
            match trySingleRead v with
            | Some v' -> v'
            | None    -> mentos.Fresh v) } 