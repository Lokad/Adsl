module Adsl.Tables


type TblId<'tag>(id: int) = struct
    member __.Id = id

    /// <summary> The construction of the scalar table is always at position zero. </summary>
    static member Scalar = TblId<'tag> 0

    override __.ToString() = sprintf "T%d" id
end

type IdxId<'tag>(id: int) = struct
    member __.Id = id

    /// <summary> The construction of the scalar index is always at position zero. </summary>
    static member Scalar = IdxId<'tag> 0

    override __.ToString() = sprintf "|%d|" id
end