# coding: utf-8

import collections
import idaapi


class InstallHxCallback(idaapi.plugin_t):
    flags = idaapi.PLUGIN_UNL
    comment = "install hx callback"
    help = "help sir"
    wanted_name = "install_hx_callback.py"
    wanted_hotkey = "$"

    def __init__(self):
        pass

    def run(self, arg_=None):
        if idaapi.remove_hexrays_callback(hx_callback):
            print "removed the callback"
        else:
            if idaapi.install_hexrays_callback(hx_callback):
                print "installed the callback"
            else:
                print "failed to install the callback"

    def init(self):
        return idaapi.PLUGIN_OK

    def term(self):
        pass


def PLUGIN_ENTRY():
    return InstallHxCallback()


def hx_callback(a=None, b=None, c=None, d=None):
    if a == idaapi.hxe_text_ready:
        did_stuff = False
        vdui = b
        cfunc = vdui.cfunc

        for n in range(10):
            if Something().auto_map_lvars(vdui, cfunc.entry_ea):
                did_stuff = True
            else:
                break
        return did_stuff
    return 0


class Something:
    def __init__(self):
        self.de = None
        self.assignments = None

    def analyze_fn(self):
        assignments = collections.defaultdict(list)
        overall_refs = collections.defaultdict(int)
        parent = None
        for item in self.de.treeitems:
            if parent is None:
                parent = item
            is_expr = item.is_expr()
            if is_expr:
                cexpr = item.to_specific_type
                parent_of_item = parent.find_parent_of(cexpr)
                if cexpr.op in [idaapi.cot_var]:
                    overall_refs[cexpr.operands['v'].idx] += 1
                    if parent_of_item.is_expr():
                        parent_cexpr = parent_of_item.cexpr
                        if parent_cexpr.op in [idaapi.cot_asg, idaapi.cot_asgsmod, idaapi.cot_asgxor,
                                               idaapi.cot_asgumod, idaapi.cot_asgadd, idaapi.cot_asgsub,
                                               idaapi.cot_asgmul, idaapi.cot_asgbor, idaapi.cot_asgband,
                                               idaapi.cot_asgushr, idaapi.cot_asgsshr,
                                               idaapi.cot_asgsdiv, idaapi.cot_asgudiv, idaapi.cot_asgshl]:
                            if cexpr == parent_cexpr.x:
                                assignments[cexpr.operands['v'].idx].append(parent_cexpr.y)
                        elif parent_cexpr.op in [idaapi.cot_preinc, idaapi.cot_predec, idaapi.cot_postinc,
                                                 idaapi.cot_postdec]:
                            assert len(parent_cexpr.operands) == 1
                            assignments[cexpr.operands['v'].idx].append(parent_cexpr)

                        elif parent_cexpr.op in [idaapi.cot_ref, idaapi.cot_memptr, idaapi.cot_xor, idaapi.cot_idx,
                                                 idaapi.cot_call, idaapi.cot_cast, idaapi.cot_memref,
                                                 idaapi.cot_smod, idaapi.cot_sdiv, idaapi.cot_lnot, idaapi.cot_bnot,
                                                 idaapi.cot_band, idaapi.cot_land, idaapi.cot_lor,
                                                 idaapi.cot_bor, idaapi.cot_eq, idaapi.cot_ne, idaapi.cot_add,
                                                 idaapi.cot_sub, idaapi.cot_fsub,
                                                 idaapi.cot_udiv, idaapi.cot_fdiv, idaapi.cot_mul, idaapi.cot_fmul,
                                                 idaapi.cot_fadd, idaapi.cot_ptr, idaapi.cot_sge,
                                                 idaapi.cot_sle, idaapi.cot_sgt, idaapi.cot_slt, idaapi.cot_ult,
                                                 idaapi.cot_ugt, idaapi.cot_ule, idaapi.cot_uge, idaapi.cot_shl,
                                                 idaapi.cot_sshr, idaapi.cot_neg, idaapi.cot_ushr, idaapi.cot_tern,
                                                 idaapi.cot_umod, idaapi.cot_comma]:
                            pass
                        else:
                            print "unhandled parent op: %s" % parent_cexpr.opname
                            idaapi.jumpto(parent_cexpr.ea)
                            raise RuntimeError

        return assignments, overall_refs

    def map_vars_used_only_once(self, vdui, overall_refs):
        for var_idx, count in overall_refs.iteritems():
            if count == 1:
                the_var = self.de.lvars[var_idx]
                if var_idx in self.assignments:
                    lhs_assignments = self.assignments[var_idx]
                    assert len(lhs_assignments) == 1
                    y = lhs_assignments[0]
                    if y.op in [idaapi.cot_var]:
                        lhs_var = the_var
                        rhs_var = self.de.lvars[y.v.idx]
                        return map_the_var(lhs_var, rhs_var, '', vdui)
                else:
                    lhs_s = [self.de.lvars[l_i] for l_i, ys in self.assignments.iteritems() for y in ys if
                             y.op == idaapi.cot_var and y.v.idx == var_idx]
                    if len(lhs_s) > 0:
                        lhs_var = lhs_s[0]
                        rhs_var = the_var
                        assert len(lhs_s) == 1
                        return map_the_var(lhs_var, rhs_var, '', vdui)
        return False

    def map_lvars(self, vdui):
        assignments2000 = {}
        for lhs_idx, ys in dict(self.assignments).iteritems():
            y_ = ys[0]
            different_from_first = [y__ for y__ in ys if y_ != y__]
            assignments2000[lhs_idx] = [y_] + different_from_first
        self.assignments = assignments2000
        assigned_once = [(lhs_idx, ys[0]) for lhs_idx, ys in dict(self.assignments).iteritems() if len(ys) == 1]
        for lhs_idx, y in assigned_once:
            lhs_var = self.de.lvars[lhs_idx]
            y, type_str_ = uncast(y)
            if y.op in [idaapi.cot_var]:
                if self.rhs_is_var(lhs_var, type_str_, vdui, y):
                    return True
            else:
                rhs_s = [l_ for l_, y_ in assigned_once if (l_ != lhs_idx) and (y_ == y)]
                if len(rhs_s) > 0:
                    if y.op in [idaapi.cot_memptr, idaapi.cot_ptr, idaapi.cot_memref]:
                        for r in rhs_s:
                            return map_the_var(lhs_var, self.de.lvars[r], type_str_, vdui)
        return False

    def rhs_is_var(self, lhs_var, type_str_, vdui, y):
        rhs_idx = y.v.idx
        rhs_var = self.de.lvars[rhs_idx]
        if (rhs_idx not in self.assignments) or ((len(self.assignments[rhs_idx]) == 1) and not rhs_var.is_arg_var):
            return map_the_var(lhs_var, rhs_var, type_str_, vdui)
        else:
            return False

    def auto_map_lvars(self, vdui=None, start_ea=None):
        func = None
        if start_ea is None:
            func = idaapi.get_func(idaapi.get_screen_ea())
            start_ea = func.startEA
        if vdui is None:
            vdui = idaapi.get_tform_vdui(idaapi.get_current_tform())
            if vdui is None:
                idaapi.jumpto(start_ea)
                vdui = idaapi.get_tform_vdui(idaapi.get_current_tform())
        if func is None:
            func = idaapi.get_func(start_ea)
        self.de = idaapi.decompile(func)
        mapped_vars = False
        did_stuff = False
        self.assignments, overall_refs = self.analyze_fn()
        if self.map_vars_used_only_once(vdui, overall_refs):
            did_stuff = True
            mapped_vars = True
        elif self.map_lvars(vdui):
            did_stuff = True
            mapped_vars = True

        if mapped_vars:
            vdui.refresh_view(True)
        elif did_stuff:
            vdui.refresh_ctext()
        return did_stuff


def is_size_mismatch(lhs_var, rhs_var):
    lhs_size = lhs_var.width
    rhs_size = rhs_var.width
    if lhs_size == rhs_size:
        return False
    if not lhs_var.is_reg_var() and rhs_var.is_reg_var():
        return False
    if not ((lhs_size == 4 and rhs_size == 8) or (lhs_size == 8 and rhs_size == 4)):
        return False
    return True


def map_the_var(lhs_var, rhs_var, type_str_, vdui):
    if lhs_var == rhs_var:
        return False
    rhs_type = rhs_var.type()
    if lhs_var.accepts_type(rhs_type):
        if lhs_var.width < rhs_var.width:
            lhs_var, rhs_var = rhs_var, lhs_var
        if lhs_var.is_result_var or lhs_var.is_arg_var:
            lhs_var, rhs_var = rhs_var, lhs_var
        if (lhs_var.is_result_var or lhs_var.is_arg_var) and (rhs_var.is_result_var or rhs_var.is_arg_var):
            return False
        if lhs_var.name == rhs_var.name + "_":
            return False
        mapping_result = vdui.map_lvar(lhs_var, rhs_var)
        size_mismatch = is_size_mismatch(lhs_var, rhs_var)
        lhs_type = lhs_var.type()
        if not mapping_result:
            if not size_mismatch:
                print "failed to map %s = %s" % (lhs_var.name, rhs_var.name)
                pass
            if not lhs_var.has_user_name:
                vdui.rename_lvar(lhs_var, rhs_var.name + "_", True)
        else:
            if rhs_type != lhs_type:
                print "%s = %s" % (type_str(lhs_type, lhs_var.name), type_str(rhs_type, rhs_var.name))
            else:
                print "%s = %s" % (lhs_var.name, rhs_var.name)
            if size_mismatch:
                print "lhs: %d rhs: %d" % (lhs_var.width, rhs_var.width)
            if lhs_var.width < rhs_var.width:
                __int64 = simple_type(5)
                if rhs_type == __int64:
                    cfunc_type = vdui.cfunc.type
                    unsigned_int = simple_type(0x27)
                    print "%s swap" % cfunc_type.swap(unsigned_int)
                    print idaapi.apply_tinfo2(vdui.cfunc.entry_ea, cfunc_type, idaapi.TINFO_DEFINITE)
                else:
                    print "oh... %s" % rhs_type.dstr()
            else:
                assert not size_mismatch

            if type_str_:
                print "rhs was cast from %s" % type_str_
            return True
    else:
        print "incompatible types"
    return False


def uncast(cexpr):
    if cexpr.op in [idaapi.cot_cast]:
        cexpr, type_str_ = cast(cexpr)
        return cexpr, type_str_
    return cexpr, None


def cast(cexpr):
    assert len(cexpr.operands) == 2
    return cexpr.operands['x'], type_str(cexpr.operands['type'])


def simple_type(n):
    ti = idaapi.tinfo_t()
    ti.create_simple_type(n)
    return ti


def type_str(the_type, name_='', extra_flags=0):
    return idaapi.print_tinfo('', 0, 0, idaapi.PRTYPE_1LINE | idaapi.PRTYPE_CPP | idaapi.PRTYPE_PRAGMA | extra_flags,
                              the_type, name_, '')
