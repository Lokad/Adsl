module Adsl.AdslAutoDiff

open Adsl.Adsl
open Adsl.Program

/// <summary> 
///     Thrown when a parameter is discovered (during auto-differentiation) 
///     to not have a gradient. 
/// </summary>
let failNoGradientForParameter (adsl: Program<_>) (p: int) =
    failwith <| sprintf "%ith parameter has no gradient" p

/// <summary> Emits the adjoint of a map operation as a sequence of statements. </summary>
/// <remarks>
///     The general principle is that the derivative of `w = f(r)` can be
///     expressed as `r' = f'(r, w, w')` and `mapAdjoint` emits the inlined 
///     definition of f' for each map-function f.
/// </remarks>
/// <param name="w"> The variable to which the map was assigned. </param>
/// <param name="f"> The differentiable map operation, includes read variables. </param>
/// <param name="w'"> The adjoint of `w`. </param>
/// <param name="mentos"> To create fresh variables. </param>
/// <param name="adjointOf"> 
///     Called on one of the variables read by `f`, will return a not-yet-assigned
///     variable to which the adjoint of the read variable should be assigned.
/// </param>
/// <param name="reuse">
///     To be called on w, or on any variables present in f, if they are to be 
///     included in the returned statements. Does not need to be called on w'
/// </param>
let mapAdjoint w f w' (mentos: _ AdslMentos) adjointOf reuse = seq {
    match f with 

    | Sub (ra, rb) -> 
        // w = ra - rb
        //   =>
        // ra' = w'
        // rb' = -w'
        yield AdslVar(adjointOf ra, w')
        yield AdslMap(adjointOf rb, Minus w')

    | Minus r -> 
        // w = -r
        //   =>
        // r' = -w'
        yield AdslMap(adjointOf r, Minus w')

    | Mul (ra, rb) ->
        // w = ra * rb
        //   =>
        // ra' = w' * rb
        // rb' = w' * ra
        yield AdslMap(adjointOf ra, Mul (w', reuse rb))
        yield AdslMap(adjointOf rb, Mul (w', reuse ra))

    | Div (ra, rb) -> 
        // w = ra / rb
        //   =>
        // ra' = w' / rb
        // t1  = rb * rb
        // t2  = w' / t1
        // t3  = -t2
        // rb' = ra * t3 = -w' * ra/rb²
        let t1 = mentos.Fresh w
        let t2 = mentos.Fresh w
        let t3 = mentos.Fresh w
        yield AdslMap(adjointOf ra, Div(w', reuse rb))
        yield AdslMap(t1, Mul(reuse rb, reuse rb))
        yield AdslMap(t2, Div(w', t1))
        yield AdslMap(t3, Minus t2)
        yield AdslMap(adjointOf rb, Mul(reuse ra, t3))

    | GradControl (ra, rb) ->
        // w = gradControl(ra, rb)
        //   =>
        // ra' = w' * rb
        yield AdslMap(adjointOf ra, Mul(w', reuse rb))

    | Exp r ->
        // w = exp r
        //   =>
        // r' = w' * w = w' * exp r
        yield AdslMap(adjointOf r, Mul(w', reuse w))

    | Log r -> 
        // w = log r
        //   =>
        // r' = w' / r
        yield AdslMap(adjointOf r, Div(w', reuse r))

    | Sqrt r -> 
        // w = sqrt(r)
        //   =>
        // t1 = 0.5
        // t2 = t1 / w
        // r' = w' * t2 = w' * 0.5 / sqrt(r)
        let t1 = mentos.Fresh w
        let t2 = mentos.Fresh w
        yield AdslRawLoad(t1, AdslNumber 0.5f)
        yield AdslMap(t2, Div(t1, reuse w))
        yield AdslMap(adjointOf r, Mul(w', t2))

    | Pow (ra, rb) -> 
        // w = ra ^ rb
        //   =>
        // t1 = 1
        // t2 = rb - t1
        // t3 = ra ^ t2
        // t4 = rb * t3
        // ra' = w' * t3 = w' * rb * ra ^ (rb - 1)
        // t5 = log ra
        // t6 = w * t5
        // rb' = w' * t6 = w' * log ra * ra ^ rb
        let t1 = mentos.Fresh w
        let t2 = mentos.Fresh w
        let t3 = mentos.Fresh w
        let t4 = mentos.Fresh w
        let t5 = mentos.Fresh w
        let t6 = mentos.Fresh w
        yield AdslRawLoad(t1, AdslNumber 1.0f)
        yield AdslMap(t2, Sub(reuse rb, t1))
        yield AdslMap(t3, Pow(reuse ra, t2))
        yield AdslMap(t4, Mul(reuse rb, t3))
        yield AdslMap(adjointOf ra, Mul(w', t4))
        yield AdslMap(t5, Log(reuse ra))
        yield AdslMap(t6, Mul(reuse w, t5))
        yield AdslMap(adjointOf rb, Mul(w', t6))

    | Square r -> 
        // w = r^2
        //   =>
        // t1 = 2
        // t2 = t1 * r
        // r' = t2 * w'
        let t1 = mentos.Fresh w
        let t2 = mentos.Fresh w
        
        yield AdslRawLoad(t1, AdslNumber 2.0f)
        yield AdslMap(t2, Mul(t1, reuse r))
        yield AdslMap(adjointOf r, Mul(w', t2))
    
    | Round r -> 
        // w = round(r)
        //   =>
        // r' = w'
        yield AdslVar(adjointOf r, w')
}

/// <summary>
///     Emit a copy of the loop to export the initial state as an array.
/// </summary>
let extractLoopState reuse mentos (loop:AdslLoop<'t>) =

    if loop.State.Length = 0 then [| |], None 
    else

    let remap = remapper mentos

    let intermediateStatesSaved = 
        Array.map 
            (fun _ -> mentos.FreshFromScratch [| Types.ValType.Number |] loop.Table) 
            loop.State

    let broadcasts = [|
        for b in loop.Broadcasts do   
            yield { Outer = reuse b.Outer
                    Inner = remap b.Inner 
                    IndexPair = b.IndexPair }|]

    let inArrays = [|
        for a in loop.InArrays do
            yield { Array = reuse a.Array ; Scalar = remap a.Scalar } |]

    let states = 
        loop.State 
        |> Array.map (fun s ->
            {
                OuterInit  = Option.map reuse s.OuterInit
                OuterFinal = None
                InnerInit  = remap s.InnerInit
                InnerFinal = remap s.InnerFinal
            })

    let statements = 
        loop.Statements |> Array.map (fun s -> s.Map remap)

    let outArrays = [|
        for j = 0 to loop.State.Length - 1 do 
            yield { Array  = intermediateStatesSaved.[j]
                    Scalar = remap loop.State.[j].InnerInit } |]

    intermediateStatesSaved, 
    Some { 
        OutArrays  = outArrays 
        Sums       = Array.empty 
        InArrays   = inArrays
        Broadcasts = broadcasts
        Statements = statements
        State      = states
        DebugName  = loop.DebugName
        Table      = loop.Table
        Reverse    = loop.Reverse }
    


/// <summary>
///     Automatically differentiate an ADSL program in 
///     SSA-SA form. 
/// </summary>
let differentiate (adsl: Program<'t>): Program<'t> = 

    // For each variable, create an adjoint variable when encountering
    // the read for that variable (if that read is differentiable). 
    // When encountering the write of that variable, if an adjoint was
    // created, use that, otherwise assume 0.
    
    let adjoints = Array.create adsl.Mentos.Count None

    let adjointOf (mv: AdslVar<'t>) = 
        match adjoints.[mv.Id] with
        | Some mvd -> mvd
        | None     -> let mvd = adsl.Mentos.Fresh mv
                      adjoints.[mv.Id] <- Some mvd
                      mvd

    let tryAdjointOf (mv: AdslVar<'t>) = adjoints.[mv.Id]

    // For each parameter, the variables containing its adjoint. 

    let paramAdjoints = Array.create adsl.Meta.Parameters.Length []

    // This function returns the reverse pass corresponding to the forward pass
    // statements provided. 
    // 
    // We don't produce the forward+backward pass together at the same time, 
    // because we usually need to inject a few statements between the passes or
    // after the backward pass has ended, so it helps to have access to the 
    // backward pass as a separate sequence.

    let rec reverseOfStatements reuse (stmts: AdslStmt<_>[]): AdslStmt<_> seq = seq {  
        
        // Traverse the forward pass statements in reverse order, 
        // differentiating each of them individually
        for s = stmts.Length - 1 downto 0 do 
            match stmts.[s] with
            | AdslRawLoad _ | AdslRawMap _ | AdslRawEpoch _ -> 
                // Raw statements have no gradient contribution
                () 

            | AdslParam (w, p) -> 
                // Remember the gradient for the parameter
                match tryAdjointOf w with 
                | None    -> ()
                | Some w' -> paramAdjoints.[p] <- w' :: paramAdjoints.[p]

            | AdslVar (w, r) -> 
                // w = r 
                //   => 
                // r' = w'
                match tryAdjointOf w with 
                | None    -> ()
                | Some w' -> yield AdslVar(adjointOf r, w')

            | AdslAdd (w, rs) -> 
                // w = r1 + r2
                //   =>
                // r1', r2' = w'
                match tryAdjointOf w with 
                | None    -> ()
                | Some w' -> yield AdslTup (Array.map adjointOf rs, w') 

            | AdslTup (ws, r) -> 
                // w1, w2 = r
                //   =>
                // r' = w1' + w2'
                match Array.choose tryAdjointOf ws with 
                | [| |]    -> ()
                | [| w' |] -> yield AdslVar(adjointOf r, w')
                | ws'      -> 
                    let r' = adjointOf r
                    let tblid = r.Table
                    let scalarTblid = Tables.TblId<_>.Scalar
                    if tblid = scalarTblid then yield AdslAdd(r', ws')
                    else 
                    let innerWs' = Array.map (fun _ -> adsl.Mentos.FreshFromScratch [| Types.ValType.Number |] scalarTblid) ws'
                    let innerR = adsl.Mentos.FreshFromScratch [| Types.ValType.Number |] scalarTblid

                    let loop = { 
                        Statements = [| AdslAdd(innerR, innerWs') |] 
                        Sums       = Array.empty
                        State      = Array.empty
                        OutArrays  = [| {Scalar = innerR ; Array = r'} |] 
                        InArrays   = Array.zip ws' innerWs'|> Array.map (fun (w, iw) -> {Scalar = iw ; Array = w}) 
                        Broadcasts = Array.empty
                        Reverse    = false 
                        Table      = tblid
                        DebugName  = "loop created for array vraiable tupling" }

                    yield AdslLoop loop

            | AdslMap (w, m) -> 
                match tryAdjointOf w with 
                | None -> ()
                | Some w' -> yield! mapAdjoint w m w' adsl.Mentos adjointOf reuse

            | AdslLoop loop ->

                // To understand this section, remember that a loop is 
                // fundamentally `wi = L(ri)` and so differentiating
                // it becomes `ri' = L'(ri, wi, wi')`. 
                // 
                // We reduce this to `ri' = L'(ri, wi')` because the 
                // wi' themselves are either sums (the value of which 
                // cannot have an effect on the gradient) or output arrays, 
                // which can be recomputed from the ri instead. 
                //
                // Don't worry if not all the ri or wi' are used by 
                // the L', dead code elimination will get them.

                // Since a copy of the body of this loop already exists in 
                // the list of statements, we cannot let it keep its variables,
                // so we create a remapper that will be invoked on all the 
                // variables _inside_ the loop.

                // We emit a copy of the loop to export the initial 
                // state as an array as it is needed for the reverse pass
                let intermediateStatesSaved, optLoop = 
                    extractLoopState reuse adsl.Mentos loop

                match optLoop with 
                | None -> ()
                | Some v -> yield AdslLoop v

                // Remapper, since loop variables already appear in the forward pass.
                let remap = remapper adsl.Mentos

                // L' inputs include all L inputs and any existing
                // adjoints of L outputs.
                //
                // Note the duality between sum and broadcast.

                let broadcasts = [|
                    for b in loop.Broadcasts do   
                        yield { Outer = reuse b.Outer
                                Inner = remap b.Inner 
                                IndexPair = b.IndexPair }
                    for s in loop.Sums do 
                        match tryAdjointOf s.Outer with 
                        | None -> ()
                        | Some w' -> yield { Outer = w'     
                                             Inner = adjointOf s.Inner 
                                             IndexPair = s.IndexPair } |]

                let inArrays = [|
                    for a in loop.InArrays do
                        yield { Array = reuse a.Array ; Scalar = remap a.Scalar }
                    for a in loop.OutArrays do 
                        match tryAdjointOf a.Array with 
                        | None -> ()
                        | Some w' -> yield { Array = w' ; Scalar = adjointOf a.Scalar }

                    // As explained above, we need the innerInit precomputed in reverse order.
                    for s = 0 to loop.State.Length - 1 do 
                        yield { Array  = intermediateStatesSaved.[s] 
                                Scalar = remap loop.State.[s].InnerInit} |]

                // differentiating 
                //      `i -> (s <-> f) -> x`
                // gives
                //      `x' -> (f' <-> s') -> i'`
                let states = 
                    loop.State
                    |> Array.map (fun s ->{
                        OuterInit  = Option.bind tryAdjointOf s.OuterFinal
                        OuterFinal = Option.map adjointOf s.OuterInit
                        InnerInit  = adjointOf s.InnerFinal
                        InnerFinal = adjointOf s.InnerInit
                        }
                    )

                // Once inputs (including adjoints) are ready, can reverse the 
                // loop body itself.

                let statements = [|

                    // Use the remapper to generate a fresh forward pass
                    // (most of it, we hope, will be dead code).
                    for stmt in loop.Statements do yield stmt.Map remap 

                    // Also generate a backwards pass (from the original forward pass,
                    // to which the adjoints are associated).
                    yield! reverseOfStatements remap loop.Statements

                |]

                // L' outputs are the gradients for all L inputs.
   
                let sums =
                    loop.Broadcasts 
                    |> Array.choose (fun b -> 
                        tryAdjointOf b.Inner
                        |> Option.map (fun w' -> {
                            Inner = w'
                            Outer = adjointOf b.Outer
                            IndexPair = b.IndexPair }))

                let outArrays = 
                    loop.InArrays
                    |> Array.choose (fun a -> 
                        tryAdjointOf a.Scalar 
                        |> Option.map (fun w' -> { Array = adjointOf a.Array ; Scalar = w' }))

                yield AdslLoop { 
                        Statements = statements 
                        Sums       = sums
                        State      = states
                        OutArrays  = outArrays 
                        InArrays   = inArrays 
                        Broadcasts = broadcasts
                        Reverse    = intermediateStatesSaved.Length > 0 
                        Table      = loop.Table
                        DebugName  = loop.DebugName }

            | AdslCond cond ->

                // To understand this section, remember that a conditional
                // block is fundamentally `wi = C(ri)`, and so differentiating
                // it yields `ri' = C'(ri, wi, wi')`, which we shorten to 
                // `ri' = C'(ri, wi')` because the `wi` can be computed from 
                // the `ri`. 

                // Since a copy of the ifTrue/ifFalse already exists in 
                // the list of statements, we cannot let it keep its variables,
                // so we create a remapper that will be invoked on all the 
                // variables _inside_ the block.

                let remap = remapper adsl.Mentos

                // Inputs of C' are all outputs of C for which a gradient
                // is computed, plus all inputs of C.

                let psi = [|
                    for phi in cond.Phis do
                        match phi with 
                        | Phi (w, rt, rf) -> 
                            match tryAdjointOf w with 
                            | None -> ()
                            | Some w' -> yield Psi(adjointOf rt, adjointOf rf, w')
                        | PhiT    (w, rt) -> 
                            match tryAdjointOf w with
                            | None -> ()
                            | Some w' -> yield PsiT(adjointOf rt, w')
                        | PhiF    (w, rf) -> 
                            match tryAdjointOf w with 
                            | None -> ()
                            | Some w' -> yield PsiF(adjointOf rf, w')
                    for psi in cond.Psis do 
                        match psi with 
                        | Psi (wt, wf, r) -> yield Psi(remap wt, remap wf, reuse r)
                        | PsiT    (wt, r) -> yield PsiT(remap wt, reuse r)
                        | PsiF    (wf, r) -> yield PsiF(remap wf, reuse r) |]

                // Each block is differentiated in the same way: 
                //  - remap all variables in the forward pass
                //  - followed by reverse pass 

                let ifFalse = [|
                    for stmt in cond.IfFalse do yield stmt.Map remap 
                    yield! reverseOfStatements remap cond.IfFalse |]

                let ifTrue = [|
                    for stmt in cond.IfTrue do yield stmt.Map remap 
                    yield! reverseOfStatements remap cond.IfTrue |]

                // Outputs of C' are inputs of C for which a gradient was
                // computed by the loop.

                let phi = cond.Psis |> Array.choose (fun psi ->
                    let wt', wf', r = 
                        match psi with 
                        | Psi (wt, wf, r) -> tryAdjointOf wt, tryAdjointOf wf, r
                        | PsiT    (wt, r) -> tryAdjointOf wt, None, r
                        | PsiF    (wf, r) -> None, tryAdjointOf wf, r
                    match wt', wf' with 
                    | None,     None     -> None
                    | Some wt', None     -> Some <| PhiT(adjointOf r, wt')
                    | None,     Some wf' -> Some <| PhiF(adjointOf r, wf')
                    | Some wt', Some wf' -> Some <| Phi(adjointOf r, wt', wf'))

                yield AdslCond {
                    IfTrue = ifTrue
                    IfFalse = ifFalse 
                    Phis = phi
                    Psis = psi 
                    If = reuse cond.If }
        }


    let stmts = [|
        
        // Emit all statements from the existing program
        yield! adsl.Statements
        
        // Initialize the adjoint of the loss to 1 
        yield AdslRawLoad(adjointOf adsl.Loss, AdslNumber 1.0f)
        
        // Generate the reverse pass (with 'id' as the reuse because 
        // we are using the variables for the first time - subsequent 
        // uses in AdslCond/AdslLoop will need remappings). 
        yield! reverseOfStatements id adsl.Statements

        // Ensure that each parameter is associated with exactly one var.
        // After this, 'paramAdjoints' will only contain single-element lists.
        for p = 0 to paramAdjoints.Length - 1 do 
            match paramAdjoints.[p] with 
            | []              -> failNoGradientForParameter adsl p
            | [_]             -> ()
            | (v :: _) as vs  -> let v' = adsl.Mentos.Fresh v
                                 yield AdslAdd(v', Array.ofList vs)
                                 paramAdjoints.[p] <- [v']
    |]

    {   Statements = stmts
        Loss = adsl.Loss
        Gradients = paramAdjoints |> Array.map List.head
        Metrics = adsl.Metrics
        Mentos = adsl.Mentos 
        Meta = adsl.Meta }
