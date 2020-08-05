# Copyright 2020 Reswitched Team
#
# Permission to use, copy, modify, and/or distribute this software for any purpose with or
# without fee is hereby granted, provided that the above copyright notice and this permission
# notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
# SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL
# THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY
# DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF
# CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE
# OR PERFORMANCE OF THIS SOFTWARE.

# kernel1to4.py: IDA loader for 1.0.0-4.1.0 Horizon Kernel
from __future__ import print_function

try:
    from unicorn import *
    from unicorn.arm64_const import *

    from capstone import *
    from capstone.arm64 import *

    import idaapi
    import idc
    from idc import *

    import gzip, math, os, re, struct, sys
    from struct import unpack as up, pack as pk

    from io import BytesIO

except ImportError:
    pass
else:
    if sys.version_info[0] == 3:
        iter_range = range
        int_types = (int,)
        ascii_string = lambda b: b.decode('ascii')
        bytes_to_list = lambda b: list(b)
        list_to_bytes = lambda l: bytes(l)
    else:
        iter_range = xrange
        int_types = (int, long)
        ascii_string = lambda b: str(b)
        bytes_to_list = lambda b: map(ord, b)
        list_to_bytes = lambda l: ''.join(map(chr, l))

    class BinFile(object):
        def __init__(self, li):
            self._f = li

        def read(self, arg):
            if isinstance(arg, str):
                fmt = '<' + arg
                size = struct.calcsize(fmt)
                raw = self._f.read(size)
                out = struct.unpack(fmt, raw)
                if len(out) == 1:
                    return out[0]
                return out
            elif arg is None:
                return self._f.read()
            else:
                out = self._f.read(arg)
                return out

        def read_from(self, arg, offset):
            old = self.tell()
            try:
                self.seek(offset)
                out = self.read(arg)
            finally:
                self.seek(old)
            return out

        def seek(self, off):
            self._f.seek(off)

        def close(self):
            self._f.close()

        def tell(self):
            return self._f.tell()


    class Range(object):
        def __init__(self, start, size):
            self.start = start
            self.size = size
            self.end = start+size
            self._inclend = start+size-1

        def overlaps(self, other):
            return self.start <= other._inclend and other.start <= self._inclend

        def includes(self, other):
            return other.start >= self.start and other._inclend <= self._inclend

        def __repr__(self):
            return 'Range(0x%X -> 0x%X)' % (self.start, self.end)


    class Segment(object):
        def __init__(self, r, name, kind):
            self.range = r
            self.name = name
            self.kind = kind
            self.sections = []

        def add_section(self, s):
            for i in self.sections:
                assert not i.range.overlaps(s.range), '%r overlaps %r' % (s, i)
            self.sections.append(s)


    class Section(object):
        def __init__(self, r, name):
            self.range = r
            self.name = name

        def __repr__(self):
            return 'Section(%r, %r)' % (self.range, self.name)


    def suffixed_name(name, suffix):
        if suffix == 0:
            return name
        return '%s.%d' % (name, suffix)


    class SegmentBuilder(object):
        def __init__(self):
            self.segments = []

        def add_segment(self, start, size, name, kind):
            r = Range(start, size)
            for i in self.segments:
                assert not r.overlaps(i.range), '%s: overlap: %08lx %08lx' % (name, start, size)
            self.segments.append(Segment(r, name, kind))

        def add_section(self, name, start, end=None, size=None):
            assert end is None or size is None
            if size == 0:
                return
            if size is None:
                size = end-start
            assert size > 0
            r = Range(start, size)
            for i in self.segments:
                if i.range.includes(r):
                    i.add_section(Section(r, name))
                    return
            assert False, "no containing segment for %r" % (name,)

        def flatten(self):
            self.segments.sort(key=lambda s: s.range.start)
            parts = []
            for segment in self.segments:
                suffix = 0
                segment.sections.sort(key=lambda s: s.range.start)
                pos = segment.range.start
                for section in segment.sections:
                    if pos < section.range.start:
                        parts.append((pos, section.range.start, suffixed_name(segment.name, suffix), segment.kind))
                        suffix += 1
                        pos = section.range.start
                    parts.append((section.range.start, section.range.end, section.name, segment.kind))
                    pos = section.range.end
                if pos < segment.range.end:
                    parts.append((pos, segment.range.end, suffixed_name(segment.name, suffix), segment.kind))
                    suffix += 1
                    pos = segment.range.end
            return parts

    class Emulator:
        REGISTER_IDS = [UC_ARM64_REG_X0 + i for i in xrange(29)] + [UC_ARM64_REG_X29, UC_ARM64_REG_X30]

        def __init__(self):
            self.vbar = -1
            self.ttbr = -1
            self.tcr  = -1
            self.modified_instructions = []
            self.invalid_instructions = {
                0xD4000023 : 0xD2800000  # SMC #1 -> MOV X0, #0
            }
            # Initialize emulator in ARM mode
            self.mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)

            # Map in the start of dram, which init will execute from.
            self.mu.mem_map(0x80060000, 0x80000)
            # Map in the clock and reset controller, so kernel can try to enable all cores.
            self.mu.mem_map(0x60006000, 0x1000)
            # Map in MC_EMEM_CFG_0, and make it read the right value for main memory size.
            self.mu.mem_map(0x70019000, 0x1000)
            self.mu.mem_write(0x70019050, struct.pack('<I', (4 * 1024 * 1024 * 1024) // (1024 * 1024)))

            self.current_pc = -1
            self.last_invalid_pc = -1

        def patch_instruction(self, uc, address, value):
            old = uc.mem_read(address, len(value))
            self.modified_instructions.append((address, bytes(old)))
            uc.mem_write(address, value)

        def restore_instructions(self, uc):
            for (addr, val) in self.modified_instructions:
                uc.mem_write(addr, val)
            self.modified_instructions = []

        @staticmethod
        def hook_code(uc, address, size, self):
            assert size == 4
            insn = up('<I', uc.mem_read(address, 4))[0]
            self.restore_instructions(uc)
            if insn in self.invalid_instructions:
                self.patch_instruction(uc, address, pk('<I', self.invalid_instructions[insn]))
            if insn == 0xD4000023 and uc.reg_read(Emulator.REGISTER_IDS[0]) == 0xC3000008 and uc.reg_read(Emulator.REGISTER_IDS[1]) == 0x70019050:
                # Patch SmcReadWriteRegister to return the right memory size.
                uc.reg_write(Emulator.REGISTER_IDS[1], (4 * 1024 * 1024 * 1024) // (1024 * 1024))
            if (insn & 0xFFFFFFE0) == 0xD518C000:
                # VBAR set
                which = insn & 0x1F
                self.vbar = uc.reg_read(Emulator.REGISTER_IDS[which])
            if (insn & 0xFFFFFFE0) == 0xD5182020:
                # TTBR set
                which = insn & 0x1F
                self.ttbr = uc.reg_read(Emulator.REGISTER_IDS[which])
            if (insn & 0xFFFFFFE0) == 0xD5182040:
                # TCR set
                which = insn & 0x1F
                self.tcr = uc.reg_read(Emulator.REGISTER_IDS[which])

        def read_mem(self, addr, size):
            return bytes(self.mu.mem_read(addr, size))

        def simulate(self, pc, steps):
            self.current_pc = pc
            while True:
                try:
                    self.mu.emu_start(self.current_pc, 0xFFFFFFFFFFFFFFFF, 0, steps)
                    break
                except UcError as e:
                    self.current_pc = self.mu.reg_read(UC_ARM64_REG_PC)
                    if e.errno == UC_ERR_EXCEPTION:
                        if self.current_pc == self.last_invalid_pc:
                            break
                        else:
                            self.last_invalid_pc = self.current_pc
                            continue
                    break

        def build_mappings(self):
            self.mappings = []
            cur_start = -1
            cur_attr  = -1
            cur_phys  = -1
            base_address = (1 << 64) - (1 << (64 - self.t1sz))
            L1_SIZE, L2_SIZE, L3_SIZE = (1024 * 1024 * 1024), (2 * 1024 * 1024),  (4 * 1024)
            for i in iter_range(0, 0x1000 // (1 << (39 - (64 - self.t1sz))), 8):
                l1_entry,  = up('<Q', self.read_mem(self.ttbr + i, 8))
                if (l1_entry & 3) == 3:
                    # L1 table
                    l1_table = l1_entry & 0xFFFFF000
                    for j in iter_range(0, 0x1000, 8):
                        l2_entry, = up('<Q', self.read_mem(l1_table + j, 8))
                        if (l2_entry & 3) == 3:
                            # L2 table
                            l2_table = l2_entry & 0xFFFFF000
                            for k in iter_range(0, 0x1000, 8):
                                l3_entry, = up('<Q', self.read_mem(l2_table + k, 8))
                                if (l3_entry & 3) == 3:
                                    # L3 block
                                    phys = l3_entry & 0xFFFFFF000
                                    attr = (l3_entry & ~0xFFFFFF000) & ~0x0010000000000000
                                    if cur_start == -1:
                                        cur_start = base_address
                                        cur_attr  = attr
                                        cur_phys  = phys
                                    elif cur_attr != attr or phys != (cur_phys + base_address - cur_start):
                                        self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                                        cur_start = base_address
                                        cur_attr  = attr
                                        cur_phys  = phys
                                    #print('%x %x: %x' % (l2_table + k, base_address, l3_entry))
                                else:
                                    # Empty
                                    assert l3_entry == 0
                                    if cur_start != -1:
                                        self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                                        cur_start = -1
                                        cur_attr  = -1
                                        cur_phys  = -1
                                base_address += L3_SIZE
                        elif (l2_entry & 3) == 1:
                            # L2 block
                            phys = l2_entry & 0xFFFFFF000
                            attr = (l2_entry & ~0xFFFFFF000) & ~0x0010000000000000
                            if cur_start == -1:
                                cur_start = base_address
                                cur_attr  = attr
                                cur_phys  = phys
                            elif cur_attr != attr or phys != (cur_phys + base_address - cur_start):
                                self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                                cur_start = base_address
                                cur_attr  = attr
                                cur_phys  = phys
                            #print('%x %x: %x' % (l1_table + j, base_address, l2_entry))
                            base_address += L2_SIZE
                        else:
                            # Empty
                            assert l2_entry == 0
                            if cur_start != -1:
                                self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                                cur_start = -1
                                cur_attr  = -1
                                cur_phys  = -1
                            base_address += L2_SIZE
                elif (l1_entry & 1) == 1:
                    # L1 block
                    phys = l1_entry & 0xFFFFFF000
                    attr = (l1_entry & ~0xFFFFFF000) & ~0x0010000000000000
                    if cur_start == -1:
                        cur_start = base_address
                        cur_attr  = attr
                        cur_phys  = phys
                    elif cur_attr != attr or phys != (cur_phys + base_address - cur_start):
                        self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                        cur_start = base_address
                        cur_attr  = attr
                        cur_phys  = phys
                    #print('%x %x: %x' % (self.ttbr + i, base_address, l1_entry))
                    base_address += L1_SIZE
                else:
                    # Empty
                    assert l1_entry == 0
                    if cur_start != -1:
                        self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                        cur_start = -1
                        cur_attr  = -1
                        cur_phys  = -1
                    base_address += L1_SIZE
            if cur_start != -1:
                self.mappings.append((cur_start, base_address - cur_start, cur_phys, cur_attr))
                cur_start = -1
                cur_attr  = -1
                cur_phys  = -1

        def run_emulator(self, init_base, data):
            self.mu.mem_write(init_base, data)
            h = self.mu.hook_add(UC_HOOK_CODE, Emulator.hook_code, self)

            # Run the kernel .init to generate the page tables
            self.simulate(init_base, 1500000)
            assert self.vbar != -1
            assert self.ttbr != -1
            assert self.tcr != -1

            # Walk the tables to determine what mappings the kernel made.
            self.t1sz = ((self.tcr >> 16) & 0x3F)
            self.build_mappings()

    KERNEL_INIT_SIZE  = 0x2000
    KERNEL_META_MAGIC = struct.pack('<QQQQ', 0x8006A000, 0x8006C000, 0x8006E000, 0x80070000)

    def find_kernel_meta(li):
        li.seek(0)
        init = li.read(KERNEL_INIT_SIZE)
        for i in iter_range(0, KERNEL_INIT_SIZE - len(KERNEL_META_MAGIC), 8):
            if init[i:i+len(KERNEL_META_MAGIC)] == KERNEL_META_MAGIC:
                return i
        return -1

    def accept_file(li, n):
        if not isinstance(n, int_types) or n == 0:
            li.seek(0)
            if li.read(4) == b'\xDFO\x03\xD5':
                meta_ofs = find_kernel_meta(li)
                if meta_ofs != -1:
                    return 'Switch 1.0.0-4.0.0 kernel'
        return 0

    def patch_movk_to_adrp(text_start, text, ro_rw, mappings):
        text_size = len(text)
        text_end  = text_start + text_size
        targets = set()

        def is_mapped(address):
            for (virt_addr, size, phys_addr, attr) in mappings:
                if virt_addr <= address and address <= virt_addr + size - 1:
                    return True
            return False

        for off in iter_range(0, len(ro_rw), 8):
            qw = struct.unpack_from('<Q', ro_rw, off)[0]
            if text_start <= qw < text_end and qw not in targets:
                targets.add(qw)

        md2 = Cs(CS_ARCH_ARM64, CS_MODE_ARM)
        def patch(bytes_, addr):
            assert len(bytes_) == 4
            off = addr - text_start
            #print('PATCH %x' % addr)
            for gi in md2.disasm(bytes_, addr):
                ida_bytes.patch_bytes(gi.address, bytes_)

        md = Cs(CS_ARCH_ARM64, CS_MODE_ARM)
        md.detail = True

        for insn in md.disasm(text, text_start):
            for i in insn.operands:
                if i.type in (ARM64_OP_IMM, ARM64_OP_CIMM):
                    imm = i.value.imm & 0xFFFFffffFFFFffff
                    if text_start <= imm < text_end:
                        targets.add(imm)

        def get_regname_imm_mask(insn):
            reg_name = insn.reg_name(insn.operands[0].value.reg)

            immop = insn.operands[1]
            assert immop.type == ARM64_OP_IMM
            mask = 0xFFFF
            imm = immop.value.imm
            if immop.shift.type != ARM64_SFT_INVALID:
                assert immop.shift.type == 1
                imm <<= immop.shift.value
                mask <<= immop.shift.value

            return reg_name, imm, mask

        constants = {}
        last = text_start - 8
        for offset in iter_range(0, len(text), 4):
            try:
                insn = md.disasm(text[offset:offset+4], text_start + offset).next()
            except StopIteration:
                # invalid
                #print("INVAL: 0x%x" % (text_start + offset))
                continue

            if insn.mnemonic in ('b', 'bl', 'cbz', 'cbnz', 'tbz', 'tbnz', 'ret') or insn.mnemonic.startswith('b.'):
                #print("CONT: 0x%x:\t%s\t%s" % (insn.address, insn.mnemonic, insn.op_str))
                continue

            if insn.address != last + 4 or insn.address in targets:
                constants = {}

            #print("0x%x:\t%s\t%s" % (insn.address, insn.mnemonic, insn.op_str))
            last = insn.address

            processed = False
            if insn.mnemonic in ('movz', 'movn'):
                reg_name, imm, _ = get_regname_imm_mask(insn)
                if reg_name.startswith('x'):
                    if insn.mnemonic == 'movn':
                        value = ~imm & 0xFFFFffffFFFFffff
                    else:
                        assert insn.mnemonic == 'movz'
                        value = imm
                    constants[reg_name] = {"insns": [insn], "value": value}
                    #print(reg_name + ': 0x%X' % value)
                    processed = True
            elif insn.mnemonic == 'movk':
                reg_name, imm, mask = get_regname_imm_mask(insn)

                if reg_name in constants:
                    value = constants[reg_name]['value']
                    value &= ~mask
                    value |= imm
                    constants[reg_name]['value'] = value
                    constants[reg_name]['insns'].append(insn)
                    #print(reg_name + ': 0x%X' % value)
                    processed = True

                    imm = None
                    if mask == 0xFFFF: # last 16 bits
                        #print(reg_name + ': 0x%X' % value)
                        if is_mapped(value):
                            distance = value - insn.address
                            insns = constants[reg_name]['insns']
                            if distance > 0 and (distance & 3) == 0 and len(insns) >= 2: # fix later (?)
                                if distance < 1024*1024:
                                    adr_address = insns[-1].address
                                    adr_bytes = struct.pack('I', (1<<28) | int(reg_name[1:]) | ((distance >> 2) << 5))
                                    patch(adr_bytes, adr_address)
                                    del constants[reg_name]
                                elif distance < 4*1024*1024:
                                    add_value = (value & 0xFFF)
                                    if False: # add_value == 0:
                                        adrp_address = insns[-1].address
                                        add_address = 0
                                    else:
                                        adrp_address = insns[-2].address
                                        add_address = insns[-1].address

                                    reg_num = int(reg_name[1:])

                                    base_page = adrp_address & ~0xFFF
                                    target_page = value & ~0xFFF
                                    adrp_distance = (target_page - base_page) >> 12
                                    adrp_bytes = struct.pack('I', (1<<31) | (1<<28) | reg_num | ((adrp_distance >> 2) << 5) | ((adrp_distance & 3) << 29))
                                    patch(adrp_bytes, adrp_address)
                                    if True: #add_value != 0:
                                        add_bytes = struct.pack('I', (1<<31) | (1<<28) | (1<<24) | ((0xFFF & value) << 10) | (reg_num << 5) | reg_num)
                                        patch(add_bytes, add_address)
                                    del constants[reg_name]
            if not processed:
                for k in constants.keys():
                    if k in insn.op_str or k.replace('x','w') in insn.op_str:
                        #print('invalidating %s = 0x%X' % (k, constants[k]['value']))
                        del constants[k]

    def load_file(li, neflags, fmt):
        idaapi.set_processor_type("arm", idaapi.SETPROC_LOADER_NON_FATAL|idaapi.SETPROC_LOADER)
        idc.set_inf_attr(idc.INF_LFLAGS, idc.get_inf_attr(idc.INF_LFLAGS) | idc.LFLG_64BIT)
        idc.set_inf_attr(idc.INF_DEMNAMES, idaapi.DEMNAM_GCC3)
        idaapi.set_compiler_id(idaapi.COMP_GNU)
        idaapi.add_til('gnulnx_arm64', 1)

        # Get the meta offset
        meta_ofs = find_kernel_meta(li)
        assert meta_ofs != -1

        # Read important offsets.
        li.seek(meta_ofs + 0x40)
        text_base, init_base, init_base2, kernel_end = struct.unpack('<QQQQ', li.read(0x20))

        # Load the init segment.
        li.seek(0)
        init_data = li.read(KERNEL_INIT_SIZE)

        idaapi.mem2base(init_data, init_base)

        # Emulate the kernel init segment to determine interesting extents
        emu = Emulator()
        emu.run_emulator(init_base, init_data)

        builder = SegmentBuilder()
        builder.add_segment(init_base, KERNEL_INIT_SIZE, '.init', 'RWX')
        text_phys = 0
        text_size = 0
        ro_size   = 0
        rw_size   = 0
        core_dram_mappings = []
        for (virt_addr, size, phys_addr, attr) in emu.mappings:
            print('%x, %x, %x, %x' % (virt_addr, size, phys_addr, attr))
            assert attr in [0x4000000000078B, 0x78B, 0x6000000000078B, 0x6000000000070B, 0x60000000000607, 0x60000000000709]
            if attr == 0x78B or attr == 0x4000000000078B:
                # .text
                assert virt_addr == text_base
                builder.add_segment(virt_addr, size, '.text', 'CODE')
                li.seek(phys_addr - init_base)
                idaapi.mem2base(li.read(size), virt_addr)
                text_phys = phys_addr
                text_size = size
            elif attr == 0x6000000000078B:
                # .rodata
                assert text_size != 0
                assert virt_addr == text_base + text_size
                builder.add_segment(virt_addr, size, '.rodata', 'CONST')
                li.seek(phys_addr - init_base)
                idaapi.mem2base(li.read(size), virt_addr)
                ro_size = size
            elif attr == 0x6000000000070B and virt_addr == text_base + text_size + ro_size:
                assert text_size != 0
                assert ro_size   != 0
                # .rwdata
                builder.add_segment(virt_addr, size, '.rwdata', 'DATA')
                li.seek(phys_addr - init_base)
                idaapi.mem2base(li.read(size), virt_addr)
                rw_size = size
            elif attr == 0x60000000000607:
                # IO
                DEVICES = {
                    (0x40000000, 0x40000) : '.iram',
                    (0x50041000, 0x01000) : '.gicd',
                    (0x50042000, 0x01000) : '.gicc',
                    (0x60001000, 0x01000) : '.semaphore',
                    (0x60004000, 0x01000) : '.primary_ictlr',
                    (0x60006000, 0x01000) : '.clkrst',
                    (0x60007000, 0x01000) : '.flow_ctlr',
                    (0x6000F000, 0x01000) : '.evp',
                    (0x70006000, 0x01000) : '.uart',
                    (0x7000E000, 0x01000) : '.rtc_pmc',
                    (0x70016000, 0x02000) : '.atomics',
                    (0x70019000, 0x01000) : '.mc',
                    (0x7001C000, 0x01000) : '.mc0',
                    (0x7001D000, 0x01000) : '.mc1',
                }
                assert (phys_addr, size) in DEVICES.keys()
                name = DEVICES[(phys_addr, size)]
                builder.add_segment(virt_addr, size, name, 'IO')
            elif attr == 0x6000000000070B:
                # Kernel DRAM
                if phys_addr == (emu.ttbr & ~0xFFF) and size == 0x1000:
                    builder.add_segment(virt_addr, size, '.ttbr1', 'DATA')
                else:
                    core_dram_mappings.append((virt_addr, size, phys_addr, attr))
            else:
                # Linear DRAM
                assert attr == 0x60000000000709
                idaapi.add_segm(0, virt_addr, virt_addr + size, '.linear_dram', 'DATA', idaapi.ADDSEG_SPARSE)
                segm = idaapi.get_segm_by_name('.linear_dram')
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
                idaapi.update_segm(segm)
                idaapi.set_segm_addressing(segm, 2)

        assert len(core_dram_mappings) % 5 == 0
        if len(core_dram_mappings) // 5 == 3:
            # 1.0.0-style core local mappings
            assert core_dram_mappings[0 +  0][2] == core_dram_mappings[0 +  3][2] - 0x2000
            assert core_dram_mappings[0 +  3][2] == core_dram_mappings[0 +  6][2] - 0x2000
            assert core_dram_mappings[0 +  6][2] == core_dram_mappings[0 +  9][2] - 0x2000
            assert core_dram_mappings[0 +  0][2] == core_dram_mappings[0 + 12][2]

            assert core_dram_mappings[1 + 0][2] == core_dram_mappings[1 +  3][2] - 0x2000
            assert core_dram_mappings[1 + 3][2] == core_dram_mappings[1 +  6][2] - 0x2000
            assert core_dram_mappings[1 + 6][2] == core_dram_mappings[1 +  9][2] - 0x2000
            assert core_dram_mappings[1 + 0][2] == core_dram_mappings[1 + 12][2]

            assert core_dram_mappings[2 + 0][2] == core_dram_mappings[2 +  3][2] - 0x1000
            assert core_dram_mappings[2 + 3][2] == core_dram_mappings[2 +  6][2] - 0x1000
            assert core_dram_mappings[2 + 6][2] == core_dram_mappings[2 +  9][2] - 0x1000
            assert core_dram_mappings[2 + 0][2] == core_dram_mappings[2 + 12][2]

            builder.add_segment(core_dram_mappings[0][0], 0xA000 * 4, '.core_local_regions', 'DATA')
            builder.add_segment(core_dram_mappings[3 * 4 + 0][0], core_dram_mappings[3 * 4 + 0][1], '.current_common_stack', 'DATA')
            builder.add_segment(core_dram_mappings[3 * 4 + 1][0], core_dram_mappings[3 * 4 + 1][1], '.current_main_stack', 'DATA')
            builder.add_segment(core_dram_mappings[3 * 4 + 2][0], core_dram_mappings[3 * 4 + 2][1], '.current_context', 'DATA')
        elif len(core_dram_mappings) // 5 == 4:
            # 3.0.0-style core local mappings
            assert core_dram_mappings[0 +  0][2] == core_dram_mappings[0 +  4][2] - 0x2000
            assert core_dram_mappings[0 +  4][2] == core_dram_mappings[0 +  8][2] - 0x2000
            assert core_dram_mappings[0 +  8][2] == core_dram_mappings[0 + 12][2] - 0x2000
            assert core_dram_mappings[0 +  0][2] == core_dram_mappings[0 + 16][2]

            assert core_dram_mappings[1 + 0][2] == core_dram_mappings[1 +  4][2] - 0x2000
            assert core_dram_mappings[1 + 4][2] == core_dram_mappings[1 +  8][2] - 0x2000
            assert core_dram_mappings[1 + 8][2] == core_dram_mappings[1 + 12][2] - 0x2000
            assert core_dram_mappings[1 + 0][2] == core_dram_mappings[1 + 16][2]

            assert core_dram_mappings[2 + 0][2] == core_dram_mappings[2 +  4][2] - 0x2000
            assert core_dram_mappings[2 + 4][2] == core_dram_mappings[2 +  8][2] - 0x2000
            assert core_dram_mappings[2 + 8][2] == core_dram_mappings[2 + 12][2] - 0x2000
            assert core_dram_mappings[2 + 0][2] == core_dram_mappings[2 + 16][2]

            assert core_dram_mappings[3 + 0][2] == core_dram_mappings[3 +  4][2] - 0x1000
            assert core_dram_mappings[3 + 4][2] == core_dram_mappings[3 +  8][2] - 0x1000
            assert core_dram_mappings[3 + 8][2] == core_dram_mappings[3 + 12][2] - 0x1000
            assert core_dram_mappings[3 + 0][2] == core_dram_mappings[3 + 16][2]

            builder.add_segment(core_dram_mappings[0][0], 0xE000 * 4, '.core_local_regions', 'DATA')
            builder.add_segment(core_dram_mappings[4 * 4 + 0][0], core_dram_mappings[4 * 4 + 0][1], '.current_common_stack', 'DATA')
            builder.add_segment(core_dram_mappings[4 * 4 + 1][0], core_dram_mappings[4 * 4 + 1][1], '.current_main_stack', 'DATA')
            builder.add_segment(core_dram_mappings[4 * 4 + 2][0], core_dram_mappings[4 * 4 + 2][1], '.current_idle_stack', 'DATA')
            builder.add_segment(core_dram_mappings[4 * 4 + 3][0], core_dram_mappings[4 * 4 + 3][1], '.current_context', 'DATA')

        seg_prefix = ''
        for start, end, name, kind in builder.flatten():
            idaapi.add_segm(0, start, end, seg_prefix+name, kind)
            segm = idaapi.get_segm_by_name(seg_prefix+name)
            if kind == 'CONST':
                segm.perm = idaapi.SEGPERM_READ
            elif kind == 'CODE':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_EXEC
            elif kind == 'DATA':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
            elif kind == 'BSS':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
            elif kind == 'RWX':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE | idaapi.SEGPERM_EXEC
            elif kind == 'IO':
                segm.perm = idaapi.SEGPERM_READ | idaapi.SEGPERM_WRITE
            idaapi.update_segm(segm)
            idaapi.set_segm_addressing(segm, 2)

        # Set vector types as code.
        for i, ctx in enumerate(['sp0', 'spx', 'a64', 'a32']):
            for j, kind in enumerate(['synch', 'irq', 'fiq', 'serror']):
                addr = emu.vbar + 0x200 * i + 0x80 * j
                name = '%s_%s_exception' % (kind, ctx)
                idc.create_insn(addr)
                idc.set_name(addr, name)

        # Set .init as code.
        idc.create_insn(init_base)
        idc.set_name(init_base, 'crt0')

        # Set text start as code.
        idc.create_insn(text_base)
        idc.set_name(text_base, 'HorizonKernelMain')

        # Patch movk instructions to be better understandable by ida.
        li.seek(text_phys - init_base)
        text = li.read(text_size)
        ro_rw = li.read(ro_size + rw_size)
        patch_movk_to_adrp(text_base, text, ro_rw, emu.mappings)

        return 1


