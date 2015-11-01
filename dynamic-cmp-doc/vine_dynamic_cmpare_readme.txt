1. cd vine

2. mkdir middle

3. mkdir debug

4. save_ir db1
   save_ir db2
# generate IR in binary mode
#output in the middle folder, there will be two files: db1.ir, db2.ir.
# the two file are for the trace_diff use.
# acctually  we do this because there is a stack crash problem if we create 2 IR in time, so we
create one by one and later read file. Hope someone can fix it in the future.

5. syntac db1 db2
#Filter the blocks that are syntactically the same
#In the middle folder, there will be a db1_db2.syn file, later for trace_diff use

6. trace_reader_filter -o f_t -trace t
-t: the trace from TEMU
-f_t: the output of trace_reader
#trace_reader_filter will filter the high address of the trace.

7. appreplay  -trace [f_t1] -ida [db1]  -trace2 [f_t2] -ida2 [db2]  -tag [tag] -stp-out [stp_file]
#appreplay translate the instructions to IR, flat CFG, and give tags to each basic block.
-f_t1,f_ t2: the filtered dynamic trace from  trace_reader_filter
-db1,db2: the db file from IDA sqlite plugin
-tag: the tag information from input.
#note: the tag file¡¯s format must be strict to :
[start_index]\space[end_index]\return
this tag file must edit in linux format, or else there will be exception.
e.g. 10bytes belong to 3 tags, the tag file is following:

0 3
4 6
7 9


stp_file: by default, it will generate stp file of this trace, but I¡¯ve commented this part, if you want
to use it, just reuse the code.
However, you must use this argument even u don¡¯t want to have STP file.
#the output of appreplay will be in the middle folder, later for trace_diff use, so make sure the db name is consistent with trace_diff

8. trace_diff db1 db2
#Do the block comparision.For the blocks that have the same color, compare first(cmp_color_bbs).
#Then for blocks between the matched color blocks, complare them pair by pair(cmp_sub_bb).
-db1,db2: the db file from IDA sqlite plugin


