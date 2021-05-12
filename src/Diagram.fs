module Adsl.Diagram

open Adsl.Tables

/// <summary> Describes an upstream/downstream relationship between two tables. </summary>
type TableRelation<'tag> = {

    /// <summary> The upstream table. </summary>
    Up : TblId<'tag>

    /// <summary> The downstream table. </summary>
    Down : TblId<'tag>

    /// <summary> The thin index when broadcasting from `Up` into `Down`. </summary>
    Thin : IdxId<'tag>

    /// <summary> The fat index when broadcasting from `Up` into `Down`. </summary>
    Fat : IdxId<'tag>
} with 

    member self.Force<'o>() = {
        Up = TblId<'o> self.Up.Id
        Down = TblId<'o> self.Down.Id
        Thin = IdxId<'o> self.Thin.Id 
        Fat = IdxId<'o> self.Fat.Id }

/// <summary> A kind of table. Every table in a diagram has a kind. </summary>
/// <remarks> 
///     A table that appears as a key <see cref="Diagram{F}.LoopFiltered"/>
///     has the same kind as its unfiltered equivalent. 
/// </remarks>
type [<NoComparison;NoEquality>] TableKind<'f> = 
    /// <see cref="Diagram{F}.Observation"/>
    | TbkObservation 
    /// <summary> The scalar table. </summary>
    | TbkScalar
    /// <see cref="Diagram{F}.Upstream"/>
    | TbkUpstream of TableRelation<'f> list
    /// <see cref="Diagram{F}.Downstream"/>
    | TbkDownstream of TableRelation<'f> list
    /// <see cref="Diagram{F}.UpstreamCross"/>
    /// <remarks>
    ///     The left-table will be either an upstream table or the observation
    ///     table. The right-table will be a full table. 
    /// </remarks>
    | TbkCross of Left: TblId<'f> * Right: TblId<'f>
    /// <summary> Tables unrelated to the observation table in any way. </summary>
    /// <remarks> Will necessarily be small. </remarks>
    | TbkFull of TblId<'f>
    
with 
    
    /// <summary> True if values from this table are loaded as scalars. </summary>
    member self.LoadedAsScalar = 
        match self with 
        | TbkScalar 
        | TbkObservation 
        | TbkUpstream _ -> true
        | _ -> false

    member self.Force<'t>() = 
        match self with 
        | TbkScalar -> TbkScalar
        | TbkObservation -> TbkObservation
        | TbkUpstream l -> TbkUpstream (l |> List.map (fun r -> r.Force<'t>()))
        | TbkDownstream l -> TbkDownstream (l |> List.map (fun r -> r.Force<'t>()))
        | TbkCross (l, r) -> TbkCross (TblId<'t> l.Id, TblId<'t> r.Id)
        | TbkFull t -> TbkFull (TblId<'t> t.Id)

