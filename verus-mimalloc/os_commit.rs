use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use vstd::iset_lib::*;
use vstd::raw_ptr::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;


verus!{

pub fn os_commit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (res: (bool, bool))
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        addr@.provenance == old(mem).points_to.provenance(),
        //old(mem).has_pointsto_for_all_read_write(),
    ensures ({
        let (success, is_zero) = res;
        mem.wf()
        //&& mem.has_pointsto_for_all_read_write()
        //&& (success ==> mem.os_has_range_read_write(addr as int, size as int))
        && mem.has_new_pointsto(&*old(mem))
        && mem.os.dom() == old(mem).os.dom()
        && mem.points_to.provenance() == old(mem).points_to.provenance()
        && (success ==> mem.os_has_range_read_write(addr as int, size as int))
    })
{
    os_commitx(addr, size, true, false, Tracked(&mut *mem))
}

pub fn os_decommit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (success: bool)
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        old(mem).pointsto_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        addr@.provenance == old(mem).points_to.provenance(),
    ensures
        mem.wf(),
        mem.os.dom() =~= old(mem).os.dom(),

        mem.points_to.dom().subset_of(old(mem).points_to.dom()),
        mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        mem.points_to.provenance() == old(mem).points_to.provenance(),

        old(mem).points_to.dom().to_iset() - mem.points_to.dom().to_iset()
            =~= old(mem).os_rw_bytes() - mem.os_rw_bytes(),
        old(mem).os_rw_bytes() - mem.os_rw_bytes()
            <= set_int_range(addr as int, addr as int + size),
{
    let tracked mut t = mem.split(addr as int, size as int);
    let ghost t1 = t;
    let (success, _) = os_commitx(addr, size, false, true, Tracked(&mut t));
    proof {
        mem.join(t);

        assert(t.os_rw_bytes().subset_of(t1.os_rw_bytes()));
        assert forall |p| mem.os_rw_bytes().contains(p)
            implies old(mem).os_rw_bytes().contains(p)
        by {
            if addr as int <= p < addr as int + size {
                assert(t1.os_rw_bytes().contains(p));
                assert(t.os_rw_bytes().contains(p));
                assert(old(mem).os_rw_bytes().contains(p));
            } else {
                assert(old(mem).os_rw_bytes().contains(p));
            }
        }
        assert_isets_equal!(old(mem).points_to.dom().to_iset() - mem.points_to.dom().to_iset(),
            old(mem).os_rw_bytes() - mem.os_rw_bytes(),
            p =>
        {
            if (old(mem).points_to.dom() - mem.points_to.dom()).contains(p) {
                if addr as int <= p < addr as int + size {
                    assert((t1.points_to.dom() - t.points_to.dom()).contains(p));
                    assert((t1.os_rw_bytes() - t.os_rw_bytes()).contains(p));
                    assert((old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p));
                } else {
                    assert((old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p));
                }
            }
            if (old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(p) {
                if addr as int <= p < addr as int + size {
                    assert((t1.os_rw_bytes() - t.os_rw_bytes()).contains(p));
                    assert((t1.points_to.dom() - t.points_to.dom()).contains(p));
                    assert((old(mem).points_to.dom() - mem.points_to.dom()).contains(p));
                } else {
                    assert((old(mem).points_to.dom() - mem.points_to.dom()).contains(p));
                }
            }
        });
        assert(mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()));
    }
    success
}

fn os_page_align_areax(conservative: bool, addr: usize, size: usize)
    -> (res: (usize, usize))
    requires
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
    ensures
        ({ let (start, csize) = res;
            start as int % page_size() == 0
            && csize as int % page_size() == 0
            && (size != 0 ==> start == addr)
            && (size != 0 ==> csize == size)
            && (size == 0 ==> start == 0 && csize == 0)
        })
{
    if size == 0 || addr == 0 {
        return (0, 0);
    }

    let start = if conservative {
        align_up(addr, get_page_size())
    } else {
        align_down(addr, get_page_size())
    };
    let end = if conservative {
        align_down(addr + size, get_page_size())
    } else {
        align_up(addr + size, get_page_size())
    };

    let diff = end - start;
    if diff <= 0 {
        return (0, 0);
    }
    (start, diff)
}

fn os_commitx(
    addr: *mut u8, size: usize, commit: bool, conservative: bool,
    Tracked(mem): Tracked<&mut MemChunk>
) -> (res: (bool, bool))
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() as int == 0,
        size as int % page_size() as int == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        !commit ==> old(mem).pointsto_has_range(addr as int, size as int),
        addr@.provenance == old(mem).points_to.provenance()
    ensures
        mem.wf(),
        mem.os.dom() =~= old(mem).os.dom(),
        commit ==> mem.has_new_pointsto(&*old(mem)),
        commit ==> res.0 ==> mem.os_has_range_read_write(addr as int, size as int),
        !commit ==> mem.points_to.dom().subset_of(old(mem).points_to.dom()),
        !commit ==> mem.os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        !commit ==> (old(mem).points_to.dom() - mem.points_to.dom()).congruent(
            old(mem).os_rw_bytes() - mem.os_rw_bytes()
        ),
        mem.points_to.provenance() == old(mem).points_to.provenance()
{
    let is_zero = false;
    let (start, csize) = os_page_align_areax(conservative, addr.addr(), size);
    if csize == 0 {
        return (true, is_zero);
    }
    let err = 0;

    let p = addr.with_addr(start);

    let tracked mut exact_mem = mem.split(addr as int, size as int);
    let ghost em = exact_mem;

    if commit {
        mprotect_prot_read_write(p, csize, Tracked(&mut exact_mem));
        proof {
            mem.join(exact_mem);
        }
    } else {
        // Take out points_to NOT in os_rw, so has_pointsto_for_all_read_write holds
        let tracked weird_extra = exact_mem.take_points_to_set(
              exact_mem.points_to.dom().filter(
                  |x: int| !exact_mem.os_rw_bytes().contains(x)));

        proof {
            assert forall |a: int| exact_mem.range_os_rw().contains(a)
                implies exact_mem.range_points_to().contains(a)
            by {
                assert(em.os.dom().contains(a));
                assert(set_int_range(addr as int, addr as int + size as int).contains(a));
                assert(old(mem).points_to.dom().contains(a));
                assert(em.points_to.dom().contains(a));
                assert(em.os_rw_bytes().contains(a));
            }
            assert(exact_mem.has_pointsto_for_all_read_write());
        }

        mprotect_prot_none(p, csize, Tracked(&mut exact_mem));

        proof {
            exact_mem.give_points_to_range(weird_extra);
            mem.join(exact_mem);

            assert forall |a: int|
                (old(mem).points_to.dom() - mem.points_to.dom()).contains(a)
                <==> (old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(a)
            by {
                if (old(mem).points_to.dom() - mem.points_to.dom()).contains(a) {
                    assert(vstd::set_lib::set_int_range(
                        addr as int, addr as int + size as int).contains(a));
                    assert(em.points_to.dom().contains(a));
                    assert(em.os_rw_bytes().contains(a));
                    assert(old(mem).os_rw_bytes().contains(a));
                }
                if (old(mem).os_rw_bytes() - mem.os_rw_bytes()).contains(a) {
                    assert(old(mem).os.dom().contains(a));
                    if !set_int_range(addr as int, addr as int + size as int).contains(a) {
                        assert(mem.os_rw_bytes().contains(a));
                    }
                    assert(set_int_range(addr as int, addr as int + size as int).contains(a));
                    assert(old(mem).points_to.dom().contains(a));
                    assert(em.points_to.dom().contains(a));
                    assert(em.os_rw_bytes().contains(a));
                }
            }
        }
    }

    proof {
        assert(mem.os.dom() =~= old(mem).os.dom());
    }

    // TODO bubble up error instead of panicking
    return (true, is_zero);
}

}

