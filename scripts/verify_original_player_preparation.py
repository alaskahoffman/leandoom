"""Independent continuous reaction/movement/height execution in DOS x86 bytes."""
import itertools
import random
import struct


def cases(height_cases):
    rng = random.Random(0x333B1333D0)
    signed = lambda n: ((n + 2**31) % 2**32) - 2**31
    result = []
    timers = [0, 0, 1, -1, -2147483648, 2147483647, 0, 18]
    commands = [0, 1, -1, -128, 127]
    for i, (h, d, z, ceiling, mx, my, time, cached, nm, live) in enumerate(height_cases):
        result.append((timers[i % 8], signed(rng.getrandbits(32)), rng.randrange(-32768, 32768),
                       z, z if i % 3 else signed(z - 1), ceiling,
                       rng.choice(commands), rng.choice(commands), mx, my,
                       rng.choice([149, 150, 156, 65535]), signed(rng.getrandbits(32)),
                       h, d, time, cached, nm, live))
    for z, timer, cached, live, nm, command, frame in itertools.product(
            [-1, 0, 1], [0, 1, 2, 18, -1, -2, -2147483648, 2147483647],
            [0, 1], [0, 1], [0, 1], [(0, 0), (1, 0), (0, 1), (-128, 127), (127, -128)], [149, 150]):
        result.append((timer, -2147483648, -32768, z, 0, 0x300000, *command,
                       0x7FFFFFFF, -2147483648, frame, -1, 2686976, -16384,
                       0x7FFFFFFF, cached, nm, live))
    return result


def floor_cases(height_cases):
    """Broad preparation cases plus independent floor/suit/RNG/clock seam cases."""
    inputs = cases(height_cases)
    profiles = [([5, 7, 4, 16][i % 4], [0, 1, 2100, -1][(i // 4) % 4],
                 (i // 16) % 256, [0, -1, 1][i % 3]) for i in range(len(inputs))]
    for special, suit, seed, time, timer, offset in itertools.product(
            [5, 7, 4, 16], [0, 1, -1], [0, 65, 255], [0, 1, 32], [0, 2], [0, 1]):
        inputs.append((timer, 0, 1000, 0, 0, 0x800000, 50, -40,
                       65536, -65536, 149, -1, 2686976, -16384, time, 0, 0, 1))
        profiles.append((special, suit, seed, offset))
    return inputs, profiles


def cross_check(raw, sine_table, run_table, spec, height_cases, probe, require, *, sector_dispatch=False, sector_handler=False, secret_probe=None,
                floor_damage=False, damage_probe=None, random_table=None):
    import capstone
    import unicorn as uc
    from unicorn import x86_const as x
    md = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_32)
    for name, code in raw.items():
        if name == 'sectorTableBytes':
            continue
        decoded = list(md.disasm(code, int(spec['units'][name]['code_offset'], 16)))
        require(b''.join(bytes(i.bytes) for i in decoded) == code, 'incomplete original disassembly')
    require(sum(map(bool, [sector_dispatch, sector_handler, floor_damage])) <= 1, "conflicting comparison modes")
    inputs, floor_profiles = floor_cases(height_cases) if floor_damage else (cases(height_cases), [])
    answers = [tuple(map(int, line.split())) for line in probe(
        ['player-preparation ' + ' '.join(map(str, case)) for case in inputs])]
    require(len(answers) == len(inputs), 'wrong preparation probe result count')
    signed = lambda n: ((n + 2**31) % 2**32) - 2**31
    sector_floors = [signed(case[3] + [0, -1, 1][i % 3]) for i, case in enumerate(inputs)]
    counters = [[-2147483648, -1, 0, 2147483647][i % 4] for i in range(len(inputs))]
    secrets = []
    if sector_handler:
        require(secret_probe is not None, 'missing compiled secret probe')
        secrets = [tuple(map(int, line.split())) for line in secret_probe(
            [f'secret {case[3]} {sector_floors[i]} 9 {counters[i]}' for i, case in enumerate(inputs)])]
        require(len(secrets) == len(inputs), 'wrong secret probe result count')
    damages = []
    if floor_damage:
        require(damage_probe is not None and random_table is not None and len(random_table) == 256,
                'missing floor probe or random table')
        sector_floors = [signed(case[3] + profile[3]) for case, profile in zip(inputs, floor_profiles)]
        damages = [tuple(map(int, line.split())) for line in damage_probe(
            [f'damage {case[3]} {sector_floors[i]} {profile[0]} {profile[1]} {case[14] & 0xffffffff} {profile[2]}'
             for i, (case, profile) in enumerate(zip(inputs, floor_profiles))])]
        require(len(damages) == len(inputs), 'wrong floor probe result count')
    em = uc.Uc(uc.UC_ARCH_X86, uc.UC_MODE_32)
    CODE, DATA = 0x100000, 0x800000
    em.mem_map(CODE, 0x40000)
    em.mem_map(DATA, 4096)
    for base in [0, 0x400000]:
        em.mem_map(base, 0x30000)
        em.mem_write(base + 0x5A84, sine_table)
        em.mem_write(base + 0x13584, struct.pack('<I', base + 0x7A84))
        em.mem_write(base + 0x16A90, run_table)
        if floor_damage: em.mem_write(base + 0x1261c, random_table)
    regs = [x.UC_X86_REG_EAX, x.UC_X86_REG_ECX, x.UC_X86_REG_EDX, x.UC_X86_REG_EBX,
            x.UC_X86_REG_ESP, x.UC_X86_REG_EBP, x.UC_X86_REG_ESI, x.UC_X86_REG_EDI]
    writes, visited = [], []
    em.hook_add(uc.UC_HOOK_MEM_WRITE, lambda _e, _a, addr, size, value, _u: writes.append((addr, size, value & 0xFFFFFFFF)))

    def observe(machine, addr, _size, _user):
        visited.append(addr - CODE)
        if addr - CODE in ([0x2fc39, 0x2fb76, 0x2fba0, 0x2fbd2] if floor_damage else [0x333e5] if sector_handler else [0x333e0, 0x333e5] if sector_dispatch else [0x333d0]):
            machine.emu_stop()

    em.hook_add(uc.UC_HOOK_CODE, observe)
    sines = struct.unpack('<10240i', sine_table)
    rng = random.Random(0x333d0)
    u32 = lambda n: struct.pack('<I', n & 0xFFFFFFFF)
    paths = {'movement': 0, 'reaction_skip': 0, 'walking_call': 0, 'retained_ground_disagrees_with_position': 0}
    if sector_handler or floor_damage:
        paths.update(on_floor=0, off_floor=0)
    if floor_damage:
        paths.update(rng_draw=0, rng_without_damage=0, damage=0, rng_wrap=0)
        require({p[2] for p in floor_profiles} == set(range(256)), 'missing RNG seed coverage')
    for i, (case, answer) in enumerate(zip(inputs, answers)):
        timer, angle, turn, z, floor, ceiling, f, c, mx, my, state, tics, h, d, time, cached, nm, live = case
        na, nx, ny, ns, nt, nr, nh, nd, nz, nb, ng = answer
        base = [0, 0x400000][i % 2]
        for name, code in raw.items():
            unit = spec['units'][name]
            patched = bytearray(code)
            for reloc in unit['relocations']:
                relocation_base = CODE if reloc['object'] == 1 else base
                require(reloc['object'] in (1, 3), 'unsupported relocation object')
                struct.pack_into('<I', patched, reloc['offset'], relocation_base + int(reloc['target'], 16))
            em.mem_write(CODE + int(unit['code_offset'], 16), bytes(patched))
        if not (sector_dispatch or sector_handler or floor_damage):
            em.mem_write(CODE + 0x333d0, b'\xf4')
        em.ctl_remove_cache(CODE, CODE + 0x40000)
        player, obj, sp = DATA + 32 + i % 4, DATA + 512 + (i // 4) % 4, DATA + 1024 + (i // 16) % 4
        em.mem_write(DATA, b'\xa5' * 4096)
        fields = {player: obj, player + 4: 0 if live else -1, player + 16: rng.getrandbits(32),
                  player + 20: h, player + 24: d, player + 28: rng.getrandbits(32),
                  player + 196: (rng.getrandbits(32) & ~4) | (4 if nm else 0),
                  obj + 20: z, obj + 32: angle, obj + 36: rng.getrandbits(32), obj + 40: rng.getrandbits(32),
                  obj + 56: floor, obj + 60: ceiling, obj + 72: mx, obj + 76: my,
                  obj + 96: tics, obj + 100: base + 0x15A28 + 28 * state, obj + 124: timer}
        if sector_dispatch or sector_handler or floor_damage:
            subsector, sector = DATA + 1536 + i % 4, DATA + 1792 + (i // 4) % 4
            sector_word = floor_profiles[i][0] if floor_damage else 9 if sector_handler else [0, 1, 5, 9, 0x8000, 0xFFFF][i % 6]
            fields.update({obj + 52: subsector, subsector: sector, sector + 14: 0xA5A50000 | sector_word})
        if sector_handler:
            fields.update({sector: sector_floors[i], player + 212: counters[i]})
        if floor_damage:
            special, suit, seed, _ = floor_profiles[i]
            amount, random_index = damages[i]
            draw = special in (4, 16) and suit != 0 and z == sector_floors[i]
            fields.update({sector: sector_floors[i], player + 56: suit})
            em.mem_write(base + 0x12720, u32(seed))
            em.mem_write(base + 0x1271c, u32(173))
        for addr, value in fields.items():
            em.mem_write(addr, u32(value))
        em.mem_write(player + 8, struct.pack('<bbh', f, c, turn))
        old_ground = [1, 42, 0xFFFFFFFF][i % 3] if cached else 0
        em.mem_write(base + 0x2CF90, u32(old_ground))
        em.mem_write(base + 0x2CF80, u32(time))
        initial = [rng.getrandbits(32) for _ in regs]
        initial[2], initial[4] = player, sp
        for reg, value in zip(regs, initial):
            em.reg_write(reg, value)
        em.reg_write(x.UC_X86_REG_EFLAGS, 2 | (rng.getrandbits(12) & 0x8D5))
        expected = bytearray(em.mem_read(DATA, 4096))

        def put(addr, value):
            struct.pack_into('<I', expected, addr - DATA, value & 0xFFFFFFFF)

        for addr, value in [(obj + 32, na), (obj + 72, nx), (obj + 76, ny),
                            (obj + 100, base + 0x15A28 + 28 * ns), (obj + 96, nt), (obj + 124, nr),
                            (player + 20, nh), (player + 24, nd), (player + 16, nz), (player + 28, nb)]:
            put(addr, value)
        after = initial.copy()
        after[6] = timer & 0xFFFFFFFF
        if timer:
            after[7] = (timer - 1) & 0xFFFFFFFF
        put(sp - 4, CODE + 0x333d0)
        for n, reg in enumerate([3, 1, 2, 6, 7, 5], 2):
            put(sp - 4 * n, after[reg])
        walking = timer == 0 and state == 149 and (f != 0 or c != 0)
        scratch = None
        if timer == 0 and z <= floor:
            if f:
                scratch = na >> 19
            if c:
                scratch = ((na - 0x40000000) & 0xFFFFFFFF) >> 19
        if scratch is not None:
            put(sp - 32, scratch * 4)
        if walking:
            put(sp - 36, CODE + 0x3325e)
            put(sp - 40, sines[scratch] if scratch is not None else z)
            put(sp - 44, player + 8)
            put(obj + 36, 28)
            put(obj + 40, 0)
        if sector_handler:
            out_special, out_count = secrets[i]
            put(sp - 4, CODE + 0x333e5)
            for offset, reg in zip([8, 12, 16, 20], [3, 1, 2, 6]):
                put(sp - offset, after[reg])
            put(player + 212, out_count)
            struct.pack_into('<H', expected, sector + 14 - DATA, out_special)
        if floor_damage:
            put(sp - 4, CODE + 0x333e5)
            for offset, reg in zip([8, 12, 16, 20], [3, 1, 2, 6]):
                put(sp - offset, after[reg])
            if draw: put(sp - 24, CODE + 0x2fbb5)
        writes.clear()
        visited.clear()
        try:
            em.emu_start(CODE + 0x333b1, 0, count=268 if floor_damage else 257 if sector_handler else 232 if sector_dispatch else 226)
        except uc.UcError as error:
            raise ValueError(f'preparation case {i}: {case}: {error}; PCs {visited[-12:]}') from error
        expected_exit = (0x2fc39 if amount == 0 else {5:0x2fb76, 7:0x2fba0, 4:0x2fbd2, 16:0x2fbd2}[special]) if floor_damage else 0x333e5 if sector_handler else (0x333e0 if sector_word else 0x333e5) if sector_dispatch else 0x333d0
        require(em.reg_read(x.UC_X86_REG_EIP) == CODE + expected_exit, f'no combined return at {i}')
        if sector_handler:
            require(em.reg_read(regs[0]) == obj, f'handler EAX mismatch at {i}')
        elif sector_dispatch:
            require(em.reg_read(regs[0]) == (player if sector_word else sector), f'sector argument mismatch at {i}')
        require(bytes(em.mem_read(DATA, 4096)) == bytes(expected), f'combined memory mismatch at {i}: {case}; Lean={answer}')
        require(em.reg_read(regs[4]) == sp - (20 if floor_damage else 0), f'caller stack mismatch at {i}')
        for reg in ([5, 7] if floor_damage else [1, 2, 3, 5, 6, 7]):
            require(em.reg_read(regs[reg]) == after[reg], f'preserved register {reg} mismatch at {i}')
        ground_word = struct.unpack('<I', em.mem_read(base + 0x2CF90, 4))[0]
        require(ground_word == (int(z <= floor) if timer == 0 else old_ground), f'ground word mismatch at {i}')
        require(bool(ground_word) == bool(ng), f'compiled grounding mismatch at {i}')
        call_words = [value for addr, size, value in writes if addr == sp - 4 and size == 4]
        require(call_words == ([CODE + 0x333c9, CODE + 0x333d0] if timer == 0 else [CODE + 0x333d0]) + ([CODE + 0x333e5] if sector_handler or floor_damage else []), f'CALL return words mismatch at {i}')
        require((0x333c4 in visited) == (timer == 0) and (0x30ea0 in visited) == bool(walking), f'wrong calls at {i}')
        require(0x333cb in visited and 0x33030 in visited and (0x3315d in visited if sector_dispatch or sector_handler or floor_damage else visited[-2] == 0x3315d), f'height seam/RET missing at {i}')
        allowed = {player + o for o in [16, 20, 24, 28]} | {obj + o for o in [32, 36, 40, 72, 76, 96, 100, 124]}
        allowed |= {sp - 4 * n for n in range(1, 12)} | {base + 0x2CF90}
        if sector_handler:
            allowed.add(player + 212)
            require(all((addr in allowed and size == 4) or (addr == sector + 14 and size == 2)
                        for addr, size, _ in writes), f'unexpected store at {i}')
            on_floor = z == sector_floors[i]
            require((0x2fbdc in visited) == on_floor and (0x2fb4f in visited) == on_floor, f'handler path {i}')
            paths['on_floor' if on_floor else 'off_floor'] += 1
            require(writes[-7 if on_floor else -5:][:5] ==
                    [(sp-4,4,CODE+0x333e5)] + [(sp-off,4,after[reg]) for off,reg in zip([8,12,16,20],[3,1,2,6])],
                    f'handler stack stores {i}')
        elif floor_damage:
            allowed.add(base + 0x12720)
            require(all(addr in allowed and size == 4 for addr, size, _ in writes), f'unexpected floor store at {i}')
            require(int.from_bytes(em.mem_read(base + 0x12720, 4), 'little') == random_index, f'floor RNG mismatch {i}')
            require(int.from_bytes(em.mem_read(base + 0x1271c, 4), 'little') == 173, f'misc RNG changed {i}')
            require(visited.count(0x24160) == int(draw), f'floor RNG call count {i}')
            expected_tail = [(sp-4, 4, CODE+0x333e5)] + [(sp-off, 4, after[reg]) for off, reg in zip([8,12,16,20],[3,1,2,6])]
            if draw: expected_tail += [(sp-24, 4, CODE+0x2fbb5), (base+0x12720, 4, (seed+1)%256)]
            require(writes[-len(expected_tail):] == expected_tail, f'floor write order {i}')
            if amount:
                require([em.reg_read(reg) for reg in regs[:4]] == [obj, amount, 0, 0], f'floor call arguments {i}')
            paths['on_floor' if z == sector_floors[i] else 'off_floor'] += 1
            paths['rng_draw'] += int(draw)
            paths['rng_without_damage'] += int(draw and amount == 0)
            paths['rng_wrap'] += int(draw and seed == 255)
            paths['damage'] += int(amount != 0)
        else:
            require(all(addr in allowed and size == 4 for addr, size, _ in writes), f'unexpected store at {i}')
        paths['movement' if timer == 0 else 'reaction_skip'] += 1
        paths['walking_call'] += int(bool(walking))
        paths['retained_ground_disagrees_with_position'] += int(timer != 0 and bool(cached) != (z <= floor))
    if floor_damage: require(all(paths.values()), 'missing joined floor path coverage')
    return {'cases': len(inputs), 'paths': paths, 'code_origin': '0x0', 'entry_pc': '0x333b1', 'exit_pc': [hex(p) for p in [0x2fc39,0x2fb76,0x2fba0,0x2fbd2]] if floor_damage else '0x333e5' if sector_handler else ['0x333e0', '0x333e5'] if sector_dispatch else '0x333d0',
            'data_bases': [0, 0x400000], 'unaligned_addresses': True,
            'checks': ['continuous execution', 'all motion/animation/reaction/view fields', 'full dynamic memory page',
                       'cached grounding word', 'preserved EBP/EDI' if floor_damage else 'six preserved registers', 'caller ESP', 'actual CALL return words', 'write footprint'] + (['compiled floor helper', 'continuous floor CALL/prologue/decision', 'both RNG indices', 'all four damage arguments', 'ordered floor stack/index stores'] if floor_damage else []) + (['compiled secret helper', 'continuous sector CALL/handler/RET', 'on/off sector floor'] if sector_handler else []) + (['sector dispatch', 'special-sector argument', 'no sector-handler execution'] if sector_dispatch else [])}
