module Adsl.Adsl

open Adsl.Tables
open Adsl.Types

open System.Collections.Generic


/// <summary> A variable in a adsl program. </summary>
type [<Struct;CustomEquality;NoComparison>] AdslVar<'t> = { 

    /// <summary> Internal identifier, used for equality. </summary>
    Id : int

    /// <summary> The type of value stored in this variable. </summary>
    Types : ValType[]

    /// <summary> The table in which this variable belongs. </summary>
    /// <remarks>
    ///     For scalars (including values in the upstream tables or in the 
    ///     observation table), this will be TblId.Scalar.
    ///
    ///     For arrays (including "Full" and "Cross" values), this will be 
    ///     the table of the corresponding "Full". That is, using the size
    ///     of this table is safe to iterate over this array.
    /// </remarks>
    Table : TblId<'t>
} with 

    member self.Type = 
        if self.Types.Length <> 1 then failwith "Expected non-tuple"
        self.Types.[0]

    override self.GetHashCode() = self.Id
    override self.Equals(o: obj) = 
        match o with 
        | :? AdslVar<'t> as mv -> mv.Id = self.Id
        | _ -> false

    override self.ToString() = 
        if self.Table = TblId<_>.Scalar then 
            sprintf "$%d" self.Id
        else
            sprintf "$%d[|%O|]" self.Id self.Table

/// <summary> The various types of vectors from which a adsl scalar can be loaded. </summary>
type ScalarSource = 
    | ScalarTable = 0
    | ObservationTable = 1 
    | UpstreamTable = 2
    
/// <summary> The various types of vectors from which a adsl array can be loaded. </summary>
type ArraySource = 
    | Full = 0
    | ObservationCross = 1
    | UpstreamCross = 2

/// <summary> The size of a state variable exposed to the program's loop. </summary>
type StateSource = 
    | Scalar of ScalarSource
    | Array  of ArraySource

/// <summary> A map-function applied to a set of scalar arguments. </summary>
type [<Struct;NoEquality;NoComparison>] AdslMap<'t> = {
    Function: string 
    Arguments: AdslVar<'t>[]
} with 

    member self.Map f = {
        Function  = self.Function
        Arguments = Array.map f self.Arguments
    }

// Definition of ADSL : An Automatic Differentiable Sub-Language
//
// The purpose of this intermediate language is to 1. express most 
// operations that we would want to differentiate and 2. be closed
// by differentiation (i.e. the derivative of an ADSL program is 
// also an ADSL program).
//
// ADSL is an SSA language.

/// <summary> Used to create fresh variables. </summary>
type AdslMentos<'t> = class 

    val private variables : List<AdslVar<'t>>

    new() = { variables = List() }

    /// <summary>
    ///     Create a fresh copy of a variable, with the same type and 
    ///     table as the original. 
    /// </summary>
    member self.Fresh (omv: 'o AdslVar) = 
        let mv = { Id    = self.variables.Count 
                   Types = omv.Types 
                   Table = TblId<'t>(omv.Table.Id) }
        self.variables.Add mv
        mv

    /// <summary>
    ///     Create a fresh variable, with the specified type and table. 
    /// </summary>
    member self.FreshFromScratch (mTypes: ValType[]) (table: TblId<'t>) = 
        let mv = {  Id    = self.variables.Count 
                    Types = mTypes
                    Table = table }
        self.variables.Add mv
        mv


    /// <summary> Total number of variables allocated. </summary>
    member self.Count = 
        self.variables.Count

end

/// <see cref="remapper"/>
type Remapper<'f, 't> = class

    val public Mapping : Dictionary<AdslVar<'f>, AdslVar<'t>> 

    val private mentos : AdslMentos<'t>

    new(mentos) = { Mapping = Dictionary() ; mentos = mentos }

    member self.Of (mv: AdslVar<'f>) = 
        match self.Mapping.TryGetValue mv with 
        | true, mv' -> mv'
        | false,  _ -> let mv' = self.mentos.Fresh mv
                       self.Mapping.Add(mv, mv')
                       mv'

end

/// <summary> 
///     Returns a function which associates a fresh variable
///     which each different variable that is passed in. Calling
///     on the same variable twice will return the same mapping.
/// </summary>
let remapper (mentos: AdslMentos<'t>) = (Remapper mentos).Of

/// <summary> A differentiable map-function. </summary>
/// <remarks>
///     The exhaustive list of map functions that can be included
///     in an ADSL script.
/// 
///     Note that addition is not a map-function in ADSL, but is instead treated
///     as a special operator `AdslAdd`.
///
///     Non-differentiable map-functions (such as those on booleans) can
///     still be included using `AdslRawMap`.
/// </remarks>
type DiffableMap<'t> = 
    | Mul         of AdslVar<'t> * AdslVar<'t>
    | Div         of AdslVar<'t> * AdslVar<'t>
    | Pow         of AdslVar<'t> * AdslVar<'t>
    | Sub         of AdslVar<'t> * AdslVar<'t>
    | GradControl of AdslVar<'t> * AdslVar<'t>
    | Exp    of AdslVar<'t>
    | Log    of AdslVar<'t> 
    | Square of AdslVar<'t> 
    | Sqrt   of AdslVar<'t>
    | Minus  of AdslVar<'t>
    | Round  of AdslVar<'t>

    override self.ToString() =  
        match self with
        | Div (a, b) -> sprintf "%O / %O" a b
        | Pow (a, b) -> sprintf "%O ^ %O" a b
        | Sub (a, b) -> sprintf "%O - %O" a b
        | Mul (a, b) -> sprintf "%O * %O" a b  
        | GradControl(a, b) -> sprintf "gradControl(%O, %O)" a b  
        | Sqrt     a -> sprintf "sqrt(%O)" a
        | Minus    a -> sprintf "-(%O)" a
        | Log      a -> sprintf "log(%O)" a
        | Exp      a -> sprintf "exp(%O)" a
        | Square   a -> sprintf "(%O)^2" a
        | Round    a -> sprintf "round(%O)" a

    /// <summary> All variables that appear in the operator. </summary>
    member self.ReadVariables = 
        match self with 
        | Div (a, b)  
        | Pow (a, b)  
        | Sub (a, b)  
        | GradControl (a, b)  
        | Mul (a, b) -> [| a; b |]
        | Sqrt     a  
        | Minus    a  
        | Log      a 
        | Round    a
        | Square   a
        | Exp      a -> [| a |]

    member self.Map f =
        match self with 
        | Div (a, b) -> Div (f a, f b)
        | Pow (a, b) -> Pow (f a, f b)
        | Sub (a, b) -> Sub (f a, f b)
        | Mul (a, b) -> Mul (f a, f b)
        | GradControl (a, b) -> GradControl (f a, f b)
        | Log      a -> Log (f a)
        | Sqrt     a -> Sqrt (f a)
        | Minus    a -> Minus (f a)
        | Exp      a -> Exp (f a)
        | Round    a -> Round (f a)
        | Square   a -> Square (f a)

/// <summary> 
///     SSA φ that appears at the end of a conditional block to reconcile 
///     values from the "if true" and "if false" blocks.
/// </summary>
/// <remarks>
///     The `ReadTrue` is read from the "if true" block, and the `ReadFalse`
///     from the "if false block". If not provided (e.g. PhiT or PhiF), assumed
///     to be the default value: zero or false.
///
///     The `Write` variable receives the value in the outer scope.
/// </remarks>
type Phi<'t> = 
    | Phi of Write: AdslVar<'t> * ReadTrue: AdslVar<'t> * ReadFalse: AdslVar<'t>
    | PhiT of Write: AdslVar<'t> * ReadTrue: AdslVar<'t>
    | PhiF of Write: AdslVar<'t> * ReadFalse: AdslVar<'t>
with 
    override self.ToString() = 
        match self with 
        | Phi (w, rt, rf) -> sprintf "%O <- φ(%O, %O)" w rt rf
        | PhiT    (w, rt) -> sprintf "%O <- φ(%O, _)" w rt
        | PhiF    (w, rf) -> sprintf "%O <- φ(_, %O)" w rf

    member self.ReadVariables = 
        match self with 
        | Phi (_, rt, rf) -> [| rt ; rf |]
        | PhiT     (_, r)
        | PhiF     (_, r) -> [| r |]

    member self.WrittenVariable = 
        match self with 
        | Phi  (w, _, _)
        | PhiT (w, _)
        | PhiF (w, _) -> w

    member self.WrittenVariables = 
        Seq.singleton self.WrittenVariable

    member self.Map f = 
        match self with 
        | Phi (w, rt, rf) -> Phi (f w, f rt, f rf)
        | PhiT    (w, rt) -> PhiT (f w, f rt)
        | PhiF    (w, rf) -> PhiF (f w, f rf)

/// <summary>
///     The ψ is the dual of the SSA φ. It reads a variable from the outer
///     scope of the conditional block, and makes it available in the 
///     "if true" block as `WriteTrue` and in the "if false" block as `WriteFalse`.
/// </summary>
/// <remarks>
///     The objective of introducing ψ is that, when differentiating a conditional,
///     the ψ becomes the φ and vice-versa.
/// </remarks>
type Psi<'t> = 
    | Psi of WriteTrue: AdslVar<'t> * WriteFalse: AdslVar<'t> * Read: AdslVar<'t>
    | PsiT of WriteTrue: AdslVar<'t> * Read: AdslVar<'t>
    | PsiF of WriteFalse: AdslVar<'t> * Read: AdslVar<'t>
with    
    override self.ToString() = 
        match self with 
        | Psi (wt, wf, r) -> sprintf "ψ(%O,%O) <- %O" wt wf r
        | PsiT    (wt, r) -> sprintf "ψ(%O,_) <- %O" wt r
        | PsiF    (wf, r) -> sprintf "ψ(_,%O) <- %O" wf r

    member self.ReadVariable = 
        match self with 
        | Psi (_, _, r)
        | PsiT   (_, r)
        | PsiF   (_, r) -> r

    member self.ReadVariables = Seq.singleton self.ReadVariable

    member self.WrittenVariables = 
        match self with 
        | Psi (wt, wf, _) -> [| wt ; wf |]
        | PsiT     (w, _)
        | PsiF     (w, _) -> [| w |]

    member self.Map f = 
        match self with 
        | Psi (wt, wf, r) -> Psi(f wt, f wf, f r)
        | PsiT    (wt, r) -> PsiT(f wt, f r)
        | PsiF    (wf, r) -> PsiF(f wf, f r)




type [<Struct;NoEquality;NoComparison>] IndexPair<'t> = {
    Up: IdxId<'t>
    Down: IdxId<'t>
} with 

    member self.Force<'o>() = {
        Up = IdxId<'o> self.Up.Id
        Down = IdxId<'o> self.Down.Id }

/// <summary> Used to describe an input-array or output-array in a loop. </summary>
type LoopArray<'t> = {

    /// <summary> The array variable outside the loop. </summary>
    Array : AdslVar<'t>

    /// <summary> The scalar variable inside the loop. </summary>
    Scalar : AdslVar<'t>
} with 

    member self.Map f = {
        Array = f self.Array 
        Scalar = f self.Scalar }

/// <summary> Used to describe a broadcast or sum in a loop. </summary>
type LoopBroadcastOrSum<'t> = {

    /// <summary> Variable outside the loop ; read by a broadcast, written by a sum. </summary>
    Outer : AdslVar<'t>

    /// <summary> Variable inside the loop ; read by a sum, written by a broadcast. </summary>
    Inner : AdslVar<'t>

    /// <summary> Thin/fat or Origin/Unique index pair, if non-scalar. </summary>
    IndexPair: IndexPair<'t> option 

} with 

    member self.Map f = {
        Outer = f self.Outer
        Inner = f self.Inner 
        IndexPair = self.IndexPair |> Option.map (fun p -> p.Force()) }

/// <summary> Used to represent internal state in a loop. </summary>
type LoopState<'t> = {

    /// <summary> The initial state is read from this variable before the loop. </summary>
    /// <remarks> When set to None, it means initialisation to zero. </remarks>
    OuterInit : AdslVar<'t> option

    /// <summary> The state is written to this variable before each iteration. </summary>
    InnerInit : AdslVar<'t>

    /// <summary> The state is read from this variable after each iteration. </summary>
    InnerFinal : AdslVar<'t>

    /// <summary> The state is written to this variable after the loop. </summary>
    OuterFinal : AdslVar<'t> option
} with 

    member self.Map f = {
        OuterInit = Option.map f self.OuterInit
        InnerInit = f self.InnerInit
        InnerFinal = f self.InnerFinal
        OuterFinal = Option.map f self.OuterFinal }



type [<NoEquality;NoComparison>] AdslLoad<'t> = 

    /// <summary> Load a scalar value from the specified vector. </summary>
    /// <remarks>
    ///     The vector should be in the scalar table, in the observation 
    ///     table, or in a table upstream from the observation table. 
    /// </remarks>
    | AdslLoadScalar of Vector: int * Source: ScalarSource * Table: TblId<'t> * DebugName: string
    
    /// <summary> Load an array from the specified vector. </summary>
    /// <remarks>
    ///     The vector should be in an orthogonal table, or in a cross with the 
    ///     left-table being the observation table or upstream from it.
    /// </remarks>
    | AdslLoadArray of Vector: int * Source: ArraySource * LeftTable: TblId<'t> * FullIndex: IdxId<'t> * RightIndex: IdxId<'t> * DebugName: string

    /// <summary> An explicit boolean value. </summary>
    | AdslBoolean of bool

    /// <summary> An explicit numeric value. </summary>
    | AdslNumber of float32

with 

    /// <summary> Erase the type tag forcefully. </summary>
    member self.Force<'n>() = 
        match self with 
        | AdslLoadScalar (vid, s, tid, d) -> 
            AdslLoadScalar (vid, s, TblId<'n> tid.Id, d)
        | AdslLoadArray (vid, s, ltid, iid, riid, d) -> 
            AdslLoadArray (vid, s, TblId<'n> ltid.Id, IdxId<'n> iid.Id, IdxId<'n> riid.Id, d)
        | AdslBoolean b -> 
            AdslBoolean b
        | AdslNumber n -> 
            AdslNumber n



/// <summary> An ADSL statement. </summary>
type AdslStmt<'t> = 

    /// <summary> Load a non-differentiable input from the Og. </summary>
    /// <remarks> 
    ///     This is used to import non-parameter vectors, as well as any 
    ///     constant literals. 
    /// </remarks>
    | AdslRawLoad of Write: AdslVar<'t> * Load: AdslLoad<'t>

    /// <summary> Load a differentiable parameter. </summary>
    /// <remarks> 
    ///     Parameters are identified by their position in the 
    ///     autodiff list-of-parameters. 
    ///
    ///     This operation consists in extracting the value of the parameter
    ///     for the current observation from the SgdObject itself.
    /// </remarks>
    | AdslParam of Write: AdslVar<'t> * Position: int

    /// <summary> Load current epoch. </summary>
    /// <remarks> 
    ///     This can not be included in <see cref="AdslRawLoad"/> 
    ///     as it will change during sgd execution.
    /// </remarks>
    | AdslRawEpoch of Write: AdslVar<'t>

    /// <summary> Copy the contents of another variable. </summary>
    | AdslVar of Write: AdslVar<'t> * Read: AdslVar<'t>

    /// <summary> The sum of several variables. </summary>
    | AdslAdd of Write: AdslVar<'t> * Read: AdslVar<'t>[]

    /// <summary> Copy a variable into several. </summary>
    /// <remarks> Intended to be the dual of 'AdslAdd' when differentiated. </remarks>
    | AdslTup of Write: AdslVar<'t>[] * Read: AdslVar<'t>

    /// <summary> A scalar map, differentiable. </summary>
    | AdslMap of Write: AdslVar<'t> * Map: DiffableMap<'t>

    /// <summary> A scalar map, NON-DIFFERENTIABLE. </summary>
    /// <remarks> Mostly used for boolean predicates. </remarks>
    | AdslRawMap of Write: AdslVar<'t> * Map: AdslMap<'t>

    /// <summary> A conditional block. </summary>
    | AdslCond of AdslCond<'t>

    /// <summary> A loop block. </summary>
    | AdslLoop of AdslLoop<'t>
with 

    /// <summary> All variables that this block reads from above itself. </summary>
    member self.ReadVariables =
        match self with
        | AdslRawEpoch _
        | AdslRawLoad _
        | AdslParam _       -> Seq.empty
        | AdslVar    (_, r)
        | AdslTup    (_, r) -> Seq.singleton r
        | AdslAdd    (_, r) -> Seq.ofArray r
        | AdslMap    (_, m) -> Seq.ofArray m.ReadVariables
        | AdslRawMap (_, m) -> Seq.ofArray m.Arguments
        | AdslCond    cond  -> cond.ReadVariables
        | AdslLoop    loop  -> loop.ReadVariables

    /// <summary> All variables that this block writes. </summary>
    member self.WrittenVariables = 
        match self with 
        | AdslRawEpoch w
        | AdslRawLoad (w, _)
        | AdslParam   (w, _)
        | AdslVar     (w, _)
        | AdslAdd     (w, _)
        | AdslMap     (w, _)
        | AdslRawMap  (w, _) -> Seq.singleton w
        | AdslTup     (w, _) -> Seq.ofArray w
        | AdslCond     cond  -> cond.WrittenVariables
        | AdslLoop     loop  -> loop.WrittenVariables

    member self.Map f = 
        match self with 
        | AdslRawEpoch w -> AdslRawEpoch(f w)
        | AdslRawLoad (w, l) -> AdslRawLoad(f w, l)
        | AdslParam (w, p) -> AdslParam (f w, p)
        | AdslVar (w, r) -> AdslVar(f w, f r)
        | AdslTup (ws, r) -> AdslTup(Array.map f ws, f r)
        | AdslAdd (w, rs) -> AdslAdd(f w, Array.map f rs)
        | AdslMap (w, m) -> AdslMap(f w, m.Map f)
        | AdslRawMap (w, m) -> AdslRawMap(f w, m.Map f)
        | AdslCond cond -> AdslCond (cond.Map f)
        | AdslLoop loop -> AdslLoop (loop.Map f)
        
/// <summary> A conditional block. </summary>
and [<NoEquality;NoComparison>] AdslCond<'t> = {

    /// <summary> Boolean variable containing the condition. </summary>
    If: AdslVar<'t>  

    /// <summary> 
    ///     Import existing variables into the `IfTrue` and `IfFalse`
    ///     blocks, which are not allowed to reference variables from 
    ///     the outer scope directly.
    /// </summary>
    Psis: Psi<'t>[]  

    /// <summary> Statements executed if the condition is true. </summary>
    IfTrue: AdslStmt<'t>[] 

    /// <summary> Statements executed if the condition is false. </summary>
    IfFalse: AdslStmt<'t>[]  
    
    /// <summary>
    ///     Merge variables assigned in `IfTrue` and `IfFalse` into the 
    ///     scope that contains the conditional. 
    /// </summary>
    Phis: Phi<'t>[]
} with 

    /// <summary> All variables that this block reads from the outer scope. </summary>
    member self.ReadVariables = seq { 
        yield self.If
        for psi in self.Psis do 
            match psi with 
            | Psi (_, _, r) 
            | PsiT (_, r)
            | PsiF (_, r) -> yield r }

    /// <summary> All variables that this block writes to the outer scope. </summary>
    member self.WrittenVariables = seq {
        for phi in self.Phis do 
            match phi with 
            | Phi (w, _, _) 
            | PhiT (w, _)
            | PhiF (w, _) -> yield w }

    member self.Map f = {
        If = f self.If
        IfTrue = self.IfTrue |> Array.map (fun s -> s.Map f)
        IfFalse = self.IfFalse |> Array.map (fun s -> s.Map f)
        Psis = self.Psis |> Array.map (fun psi -> psi.Map f)
        Phis = self.Phis |> Array.map (fun phi -> phi.Map f) }

    /// <summary> Helper to create an AdslCond manually </summary>
    /// <remarks> Completely abstracts away the Phi/Psi creation. </remarks>
    static member make 
        (mentos: AdslMentos<'t>) 
        (c: AdslVar<'t>) 
        (ifT: (AdslVar<'t> -> AdslVar<'t>) -> (AdslVar<'t> -> AdslVar<'t>) -> AdslStmt<'t>[])
        (ifF: (AdslVar<'t> -> AdslVar<'t>) -> (AdslVar<'t> -> AdslVar<'t>) -> AdslStmt<'t>[]) =

        // For example 
        //     AdslCond.make mentos lt 
        //         (fun read write -> [| AdslMap(write w, Minus (read a)) |])
        //         (fun read write -> [| AdslVar(write w, read a) |])
        //
        // The two functions 'ifT' and 'ifF' return the 'if true' and 'if false' 
        // blocks, respectively. They are not allowed to directly reference variables 
        // from outside the block, so the only variables accessible to them are: 
        //
        //  - Variables they create themselves using the 'mentos'
        //  - Variables 'imported' into the block using the 'read' and 'write' 
        //    callbacks. 'read' will include the variable in the Psi, while 
        //    'write' will include the variable in the Phi. 
        //
        // It is not necessary for a given variable (read or write) to be referenced
        // in both blocks - partial Phi or Psi will be used if only one side reads or
        // writes a variable.

        let mutable phi = Dictionary<AdslVar<'t>, AdslVar<'t>>()
        let write mv = match phi.TryGetValue mv with 
                       | true, mv' -> mv'
                       | _    -> let mv' = mentos.Fresh mv
                                 phi.Add(mv, mv')
                                 mv'

        let mutable psi = Dictionary<AdslVar<'t>, AdslVar<'t>>()
        let read mv = match psi.TryGetValue mv with 
                      | true, mv' -> mv'
                      | _    -> let mv' = mentos.Fresh mv
                                psi.Add(mv, mv')
                                mv'

        let ifTrue = ifT read write 

        // Preserve phi/psi generated by 'ifTrue' 

        let phiTrue = phi
        phi <- Dictionary()

        let psiTrue = psi
        psi <- Dictionary()

        let ifFalse = ifF read write

        // Combine phiTrue/phiFalse 

        AdslCond {   
            If = c
            IfTrue = ifTrue
            IfFalse = ifFalse 
            Psis = [|
                for kv in psiTrue do 
                    match psi.TryGetValue kv.Key with 
                    | false, _ -> yield PsiT(kv.Value, kv.Key)
                    | true, wf -> yield Psi(kv.Value, wf, kv.Key)
                for kv in psi do 
                    if not (psiTrue.ContainsKey kv.Key) then
                        yield PsiF(kv.Value, kv.Key) |]
            Phis = [| 
                for kv in phiTrue do 
                    match phi.TryGetValue kv.Key with 
                    | false, _ -> yield PhiT(kv.Key, kv.Value)
                    | true, rf -> yield Phi(kv.Key, kv.Value, rf) 
                for kv in phi do 
                    if not (phiTrue.ContainsKey kv.Key) then 
                        yield PhiF(kv.Value, kv.Key) |] }

and [<NoEquality;NoComparison>] AdslLoop<'t> = {
    
    /// <summary> The table being iterated over. </summary>
    Table: TblId<'t> 

    /// <summary> If true, the loop must be traversed in reverse order. </summary>
    /// <remarks> This is useful when reversing stateful loops. </remarks>
    Reverse : bool

    /// <summary> Arrays read element-by-element by the loop. </summary>
    /// <remarks>
    ///     All these arrays should exist in the table being iterated
    ///     over by this loop.
    /// </remarks>
    InArrays : LoopArray<'t>[]

    /// <summary> Broadcast inputs. </summary>
    Broadcasts: LoopBroadcastOrSum<'t>[]

    /// <summary> Execute these statements in sequence. </summary>
    Statements: AdslStmt<'t>[]

    /// <summary> Arrays written element-by-element by the loop. </summary>
    OutArrays : LoopArray<'t>[]

    /// <summary> Sum outputs. </summary>
    Sums : LoopBroadcastOrSum<'t>[]

    /// <summary> Internal state carried between iterations. </summary>
    State : LoopState<'t>[]

    /// <summary> Name used for debugging. </summary>
    DebugName: string
} with

    /// <summary> All variables that this block reads from the outer scope. </summary>
    member self.ReadVariables = seq {
        for a in self.InArrays do yield a.Array
        for b in self.Broadcasts do yield b.Outer
        for s in self.State do 
            match s.OuterInit with 
            | None -> ()
            | Some value -> yield value
        }

    /// <summary> All variables that this block writes to the outer scope. </summary>
    member self.WrittenVariables = seq {
        for a in self.OutArrays do yield a.Array
        for s in self.Sums do yield s.Outer
        for s in self.State do 
            match s.OuterFinal with 
            | None -> ()
            | Some value -> yield value
        }

    member self.Map f = {
        Table      = self.Table
        Reverse    = false
        DebugName  = self.DebugName 
        Statements = self.Statements |> Array.map (fun s -> s.Map f)
        InArrays   = self.InArrays   |> Array.map (fun a -> a.Map f) 
        Broadcasts = self.Broadcasts |> Array.map (fun b -> b.Map f)
        OutArrays  = self.OutArrays  |> Array.map (fun a -> a.Map f)
        Sums       = self.Sums       |> Array.map (fun s -> s.Map f)
        State      = self.State      |> Array.map (fun s -> s.Map f)
    }


