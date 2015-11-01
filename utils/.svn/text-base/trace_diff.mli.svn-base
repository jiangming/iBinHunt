(*type bb_range = 
{
	id: Vine_cfg.bbid;
	start_addr: int64;
	end_addr: int64;
}

type bb_input = 
{
	blk_id: Vine_cfg.bbid;
	seq : int32;
}

type tag_range = 
{
	start_byte_no: int32;
	end_byte_no: int32;
	color: int;
}

type bb_tag = 
{
	tag_blk_id: Vine_cfg.bbid;
	total_color: int;
}

val cal_trace_diff: Vine.stmt list Vine_cfg.cfg->Vine.stmt list Vine_cfg.cfg->
										Vine_cfg.bbid list->Vine_cfg.bbid list->
										(Vine_cfg.bbid, int) Hashtbl.t->(Vine_cfg.bbid, int) Hashtbl.t->
										(int64, int64 * float) Hashtbl.t->bool -> bool -> string->unit
										*)