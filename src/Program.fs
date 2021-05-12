module Adsl.Program

open Adsl.Tables
open Adsl.Adsl
open Adsl.Diagram

open System.Collections.Generic

type [<NoEquality;NoComparison>] AutodiffParamInfo<'t> = {

    /// <summary> The table in which the full parameter vector exists. </summary>
    SourceTable : TblId<'t>

    /// <summary> The type of `SourceTable` </summary>
    SourceTableKind : TableKind<'t>

    /// <summary> The primary index of the source table. </summary>
    SourceIndex : IdxId<'t>

    /// <summary> 
    ///     The index to iterate over to loop over this parameter, or the scalar
    ///     index if the parameter is loaded as a per-observation scalar. 
    /// </summary>
    UsageIndex: IdxId<'t>


    /// <summary> Lower bound (can be -infty) </summary>
    LowerBound : float32

    /// <summary> Upper bound (can be +infty) </summary>
    UpperBound : float32

    /// <summary> Optional projector used for cross parameters.</summary>
    /// <remarks> This is temporary and has to be removed.</remarks>
    OptLeftProj : (IdxId<'t> * IdxId<'t>) option

    /// <summary> 
    ///     The value of the parameter is injected into this variable
    ///     before the adsl program body is evaluated. 
    /// </summary>
    Var : AdslVar<'t>
} with 

    member self.Map f = {
        LowerBound = self.LowerBound
        UpperBound = self.UpperBound
        SourceTable = TblId<_> self.SourceTable.Id
        SourceTableKind = self.SourceTableKind.Force()
        SourceIndex = IdxId<_> self.SourceIndex.Id
        UsageIndex = IdxId<_> self.UsageIndex.Id
        Var = f self.Var
        OptLeftProj = match self.OptLeftProj with 
                        | None -> None 
                        | Some(ida, idb) -> Some(IdxId<_> ida.Id,IdxId<_> idb.Id) 
    }

type [<NoEquality;NoComparison>] AutodiffInfo<'t> = {

    /// <summary> All parameters, in order of definition. </summary>
    Parameters : AutodiffParamInfo<'t>[]

    /// <summary> Primary index of the 'epochs' table. </summary>
    Epochs : IdxId<'t>

    /// <summary> Optional current epoch value used in loss. </summary>
    /// <remarks> Set to None if not used in the loss function. </remarks>
    CurrentEpoch : AdslVar<'t> option

    /// <summary> The name provided for each metric. </summary>
    MetricNames : string[]

    /// <summary> If provided, learning rate. </summary>
    Rate : float32 option
} with 
    member self.AssociatedTableKinds =
        let dic = Dictionary<_,_>()
        for paramInfo in self.Parameters do
            if not (dic.ContainsKey paramInfo.SourceTable) then
                dic.[paramInfo.SourceTable] <- paramInfo.SourceTableKind

        dic :> IReadOnlyDictionary<_,_>

    member self.Map f = {
        Parameters = self.Parameters |> Array.map (fun p -> p.Map f)
        Rate = self.Rate
        MetricNames = self.MetricNames
        Epochs = IdxId<_> self.Epochs.Id
        CurrentEpoch = Option.map f self.CurrentEpoch
    }




/// <summary> An ADSL program. </summary> 
type Program<'t> = {

    /// <summary> The statements to execute, in order. </summary>
    Statements : AdslStmt<'t>[]

    /// <summary> 
    ///     A Mentos that was used to create all variables used in this program. 
    ///     Can be used to create additional variables that are not present 
    ///     anywhere in the program.
    /// </summary>
    Mentos : AdslMentos<'t>

    /// <summary> The value of the loss function. </summary>
    Loss : AdslVar<'t>

    /// <summary> 
    ///     The gradient of each parameter. Before automatic differentiation, 
    ///     this will be empty. 
    /// </summary>
    Gradients : AdslVar<'t>[]

    /// <summary>
    ///     Scalar numeric metrics emitted in addition to the loss/gradient
    ///     computation. Preserved by automatic differentiation.
    /// </summary>
    Metrics : AdslVar<'t>[]

    /// <summary> Metadata about the autodiff block itself. </summary>
    Meta : AutodiffInfo<'t>
} with 

    override self.ToString() = 
        
        // separated printing of variables.
        let vars (vs: AdslVar<'t> seq) sep = 
            vs |> Seq.map (fun v -> v.ToString()) |> String.concat sep

        let rec printStmt indent stmt = 
            match stmt with 
            | AdslRawEpoch w -> 
                sprintf "%s%O <- epoch\n" indent w
            | AdslRawLoad (w, l) -> 
                sprintf "%s%O <- %s\n" indent w 
                    (match l with
                    | AdslLoadScalar (vid, _, _, str) 
                    | AdslLoadArray (vid, _, _, _, _, str) -> 
                        // The array/scalar info is in the display of 'w'
                        sprintf "load %O // %s" vid str
                    | AdslBoolean true  -> "true"
                    | AdslBoolean false -> "false"
                    | AdslNumber n -> sprintf "%f" n)
            | AdslMap (w, m) -> 
                sprintf "%s%O <- %O\n" indent w m
            | AdslAdd (w, vs) -> 
                sprintf "%s%O <- %s\n" indent w (vars vs "+")
            | AdslTup (ws, r) -> 
                sprintf "%s%s <- %O\n" indent (vars ws ",") r
            | AdslVar (w, r) -> 
                sprintf "%s%O <- %O\n" indent w r
            | AdslParam (w, p) -> 
                sprintf "%s%O <- params %d // %s\n" indent w p 
                    (self.Meta.Parameters.[p].ToString())
            | AdslRawMap (w, m) -> 
                sprintf "%s%O <- %s\n" indent w
                    (match m.Function, m.Arguments with 
                    | "and", [| a ; b |] -> sprintf "%O & %O" a b
                    | "or",  [| a ; b |] -> sprintf "%O | %O" a b
                    | "not", [| a |]     -> sprintf "!%O" a
                    | "lt(num,num)",  [| a ; b |] -> sprintf "%O < %O" a b
                    | "leq(num,num)", [| a ; b |] -> sprintf "%O <= %O" a b
                    | "gt(num,num)",  [| a ; b |] -> sprintf "%O > %O" a b
                    | "geq(num,num)", [| a ; b |] -> sprintf "%O >= %O" a b
                    | _ -> 
                        sprintf "raw-map %O (%s)" m.Function
                            (m.Arguments |> Seq.map (fun a -> a.ToString()) |> String.concat ","))
            | AdslCond cond -> 
                let subindent = indent + "   "
                sprintf "%s%sif %O\n%s%selse\n%s%s"
                    (cond.Psis 
                     |> Seq.map (fun p -> sprintf "%s%O\n" indent p)
                     |> String.concat "")
                    indent cond.If
                    (cond.IfTrue
                     |> Seq.map (printStmt subindent)
                     |> String.concat "")
                    indent
                    (cond.IfFalse
                     |> Seq.map (printStmt subindent)
                     |> String.concat "")
                    (cond.Phis 
                     |> Seq.map (fun p -> sprintf "%s%O\n" indent p)
                     |> String.concat "")
            | AdslLoop loop -> 
                let subindent = indent + "   "
                sprintf "%sloop %O //%s\n%s%s%s%s%s%s%s%s"
                    indent loop.Table loop.DebugName
                    (loop.Broadcasts
                     |> Seq.map (fun a -> 
                        match a.IndexPair with 
                        | None -> sprintf "%s%O <- β(%O)\n" subindent a.Inner a.Outer
                        | Some p -> sprintf "%s%O <- β(%O, %O into %O)\n" subindent a.Inner a.Outer p.Up p.Down)
                     |> String.concat "")
                    (loop.InArrays 
                     |> Seq.map (fun a -> sprintf "%s%O <- %O\n" subindent a.Scalar a.Array)
                     |> String.concat "")
                    (loop.State
                     |> Seq.map (fun s -> sprintf "%skeep %O = %O\n" subindent s.InnerInit s.OuterInit)
                     |> String.concat "")
                    (loop.Statements
                     |> Seq.map (printStmt subindent)
                     |> String.concat "")
                    (loop.State 
                     |> Seq.map (fun s -> sprintf "%skeep %O as %O\n" subindent s.InnerFinal s.InnerInit)
                     |> String.concat "")
                    (loop.State
                     |> Seq.choose (fun s -> s.OuterFinal |> Option.map (fun f -> s.InnerInit, f))
                     |> Seq.map (fun (i, f) -> sprintf "%s%O <- kept %O\n" indent f i)
                     |> String.concat "")
                    (loop.OutArrays 
                     |> Seq.map (fun a -> sprintf "%s%O <- [%O]\n" indent a.Array a.Scalar)
                     |> String.concat "")
                    (loop.Sums 
                     |> Seq.map (fun a -> 
                        let optS = 
                            match a.IndexPair with 
                            | None -> ""
                            | Some indexPair ->
                                sprintf "%O into %O" indexPair.Up indexPair.Down
                        sprintf "%s%O <- sum(%O,%O)\n" indent a.Outer a.Inner optS)

                     |> String.concat "")
        
        sprintf "%s\ngradients %s\nloss %O\nmetrics %s\n%O"
            (self.Statements |> Seq.map (printStmt "") |> String.concat "")
            (vars self.Gradients ",")
            self.Loss
            (vars self.Metrics ",")
            self.Mentos
    
    member self.ReturnedVariables = seq {
        yield self.Loss
        yield! self.Gradients 
        yield! self.Metrics }

