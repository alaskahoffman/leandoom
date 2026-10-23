/* Read-only original DOOM 1.9 observer for pinned DOSBox-X normal core.
 * Never changes guest registers, code, data, or flags. GPL-2.0-or-later.
 */
#include <cstdio>
#include <cstdlib>
#include <cstdint>

/* ENEMY_PROFILE */

static void LeanDoomObserve(PhysPt ip) {
    static const char *output = std::getenv("LEANDOOM_DOS_TRACE");
    static FILE *trace = nullptr;
    static PhysPt code = 0, data = 0, dsbase = 0;
    static unsigned tick = 0, limit = 0;
    static bool inside = false;
    static int command[4] = {};
    static uint32_t enemy_ptrs[6] = {};
    static uint32_t shot_ptrs[10000] = {};
    if (!output || !cpu.pmode || !cpu.code.big) return;
    auto fail = [](const char *s) { std::fprintf(stderr,"original DOOM trace: %s\n",s); std::exit(2); };
    auto rd = [](PhysPt p) { return (uint32_t)mem_readd(p); };
    if (!trace) {
        // Near-call instruction bytes are unaffected by loader relocation.
        if (mem_readb(ip) != 0xe8 || rd(ip+1) != 0x12741) return;
        const uint8_t signature[] = {0xe8,0x41,0x27,0x01,0x00,0xe8,0xbc,0x9b,0x01,0x00,
                                    0xe8,0xa7,0x4e,0x00,0x00,0xe8,0xa2,0xae,0x01,0x00,0xeb,0x13};
        for (unsigned i=0;i<sizeof(signature);++i) if (mem_readb(ip+i)!=signature[i]) return;
        code=ip-0x2081a;
        dsbase=SegBase(ds);
        // Resolve data-object origin independently from several relocated operands.
        uint32_t offset=rd(code+0x24161)-0x12720;
        if (rd(code+0x24181)-0x1271c != offset ||
            rd(code+0x32f64)-0x2b408 != offset ||
            rd(code+0x32fad)-0x2ae78 != offset ||
            rd(code+0x32fe2)-0x2cf80 != offset ||
            rd(code+0x32f14)-0x2cf78 != offset ||
            rd(code+0x32f1a)-0x2cf74 != offset ||
            rd(code+0x315d9)-0x15a28 != offset ||
            rd(code+0x2d062)-0x15a28 != offset ||
            rd(code+0x20d4b)-0x2b2f8 != offset ||
            rd(code+0x20d51)-0x2b404 != offset)
            fail("relocated data operands disagree");
        data=dsbase+offset;
        const char *n=std::getenv("LEANDOOM_DOS_TICS");
        limit=n?(unsigned)std::strtoul(n,nullptr,10):0;
        if (!limit || limit>10000) fail("missing or invalid tic limit");
        trace=std::fopen(output,"w");
        if (!trace) fail("cannot open trace");
        const char *meta=std::getenv("LEANDOOM_DOS_BINDING");
        FILE *m=meta?std::fopen(meta,"w"):nullptr;
        if (!m) fail("cannot open binding evidence");
        std::fprintf(m,"{\"code_linear\":%u,\"data_linear\":%u,\"ds_base\":%u,\"cs\":%u,\"ds\":%u,\"paging\":%s}\n",
                     (unsigned)code,(unsigned)data,(unsigned)dsbase,(unsigned)SegValue(cs),(unsigned)SegValue(ds),paging.enabled?"true":"false");
        if (std::fclose(m)) fail("binding write failed");
    }
    if (ip!=code+0x2081a && ip!=code+0x2082e) return;
    if (SegBase(ds)!=dsbase) fail("data segment changed at tick boundary");
    if (paging.enabled) fail("paging is outside the validated observer profile");
    PhysPt player=data+0x2ae78;
    if (ip==code+0x2081a) {
        if (inside) fail("duplicate before-tick boundary");
        inside=true;
        command[0]=(int8_t)mem_readb(player+8);
        command[1]=(int8_t)mem_readb(player+9);
        command[2]=(int16_t)mem_readw(player+10);
        command[3]=mem_readb(player+15);
        if (tick!=0) return;
    } else {
        if (!inside) fail("after-tick without before-tick");
        inside=false;
        ++tick;
    }
    if (rd(data+0x2cf80)!=tick) fail("leveltime disagrees with observed tick count");
    uint32_t ptr=rd(player);
    if (!ptr) fail("null player mobj");
    PhysPt mo=dsbase+ptr;
    if (mo<0x100000 || mo>32*1024*1024-154) fail("player mobj outside profile RAM");
    if (rd(mo+ld_mobj_player_offset)!=player-dsbase) fail("player/mobj backlink mismatch");
    auto stateId = [&](uint32_t pointer) -> unsigned {
        if (!pointer) return 0; // S_NULL: leave the stored countdown untouched.
        uint32_t base=rd(code+0x2d062);
        if(pointer<base || (pointer-base)%28 || (pointer-base)/28>=967)
            fail("invalid psprite state pointer");
        return (pointer-base)/28;
    };
    PhysPt weapon=player+ld_player_psprites, flash=weapon+ld_psprite_stride;
    unsigned weaponState=stateId(rd(weapon+ld_psprite_state));
    unsigned flashState=stateId(rd(flash+ld_psprite_state));
    unsigned ready=rd(player+ld_player_readyWeapon), pending=rd(player+ld_player_pendingWeapon);
    if(ready>=ld_weapon_count || (pending>=ld_weapon_count && pending!=ld_no_pending_weapon))
        fail("invalid weapon selection");
    unsigned play=rd(data+0x12720), misc=rd(data+0x1271c);
    if(play>255 || misc>255) fail("RNG index out of range");
    // G_ExitLevel clears secretexit and assigns ga_completed (6).
    unsigned action=rd(data+0x2b404);
    if(action!=0 && action!=6) fail("game action outside level trace profile");
    if(action==6 && (rd(data+0x2b2f8)!=0 || tick!=limit))
        fail("exit must be normal and on the final requested tic; intermission unsupported");
    std::fprintf(trace,"{\"tick\":%u,\"command\":",tick);
    if(!tick) std::fputs("null",trace);
    else std::fprintf(trace,"[%d,%d,%d,%d]",command[0],command[1],command[2],command[3]);
    std::fprintf(trace,",\"state\":{\"levelTime\":%u,\"rng\":{\"play\":%u,\"misc\":%u},\"player\":{\"x\":%d,\"y\":%d,\"z\":%d,\"momx\":%d,\"momy\":%d,\"momz\":%d,\"angle\":%u",
      tick,play,misc,(int32_t)rd(mo+12),(int32_t)rd(mo+16),(int32_t)rd(mo+20),
      (int32_t)rd(mo+72),(int32_t)rd(mo+76),(int32_t)rd(mo+80),rd(mo+32));
    std::fprintf(trace,",\"health\":%d,\"armor\":%d,\"armorType\":%d,\"readyWeapon\":%u,\"pendingWeapon\":",
        (int32_t)rd(player+ld_player_health),(int32_t)rd(player+ld_player_armor),
        (int32_t)rd(player+ld_player_armorType),ready);
    if(pending==ld_no_pending_weapon) std::fputs("null",trace);
    else std::fprintf(trace,"%u",pending);
    std::fputs(",\"ammo\":[",trace);
    for(unsigned i=0;i<ld_ammo_count;++i)
        std::fprintf(trace,"%s%d",i?",":"",(int32_t)rd(player+ld_player_ammo+i*ld_ammo_stride));
    std::fprintf(trace,"],\"secrets\":%d},\"weapon\":{\"state\":%u,\"tics\":%d,\"x\":%d,\"y\":%d,\"flashState\":%u,\"flashTics\":%d,\"refire\":%d,\"extraLight\":%d}",
        (int32_t)rd(player+ld_player_secrets),weaponState,(int32_t)rd(weapon+ld_psprite_tics),
        (int32_t)rd(weapon+ld_psprite_x),(int32_t)rd(weapon+ld_psprite_y),flashState,
        (int32_t)rd(flash+ld_psprite_tics),(int32_t)rd(player+ld_player_refire),(int32_t)rd(player+ld_player_extraLight));
    // Enumerate live mobj thinkers without dereferencing removed/freed slots.
    // Bind identities at initialization using all five WAD spawnpoint shorts.
    bool live[6] = {};
    uint32_t sentinel=rd(code+0x32f1a), node=rd(data+0x2cf78);
    unsigned visited=0, found=0, shot_count=0;
    while(node!=sentinel) {
        PhysPt a=dsbase+node;
        if(++visited>10000 || a<0x100000 || a>32*1024*1024-154) fail("invalid thinker list");
        uint32_t function=rd(a+8);
        if(function==rd(code+0x31643)) {
            unsigned type=rd(a+ld_type);
            // Select by type, not MF_MISSILE: explosions keep the same type.
            if(type==ld_shot_type) shot_ptrs[shot_count++]=node;
            if(type==1 || type==11) {
                int index=-1;
                for(unsigned j=0;j<6;++j) {
                    bool match=type==ld_enemy_types[j];
                    for(unsigned k=0;k<5;++k) match=match && (int16_t)mem_readw(a+ld_spawnpoint+2*k)==ld_enemy_spawns[j][k];
                    if(match) { if(index!=-1) fail("ambiguous enemy identity"); index=(int)j; }
                }
                if(index<0 || live[index]) fail("unknown/duplicate enemy spawnpoint");
                if(!tick) enemy_ptrs[index]=node;
                if(enemy_ptrs[index]!=node) fail("enemy identity changed; respawn unsupported");
                live[index]=true; ++found;
            }
        }
        node=rd(a+4);
    }
    if(!tick && found!=6) fail("missing initialized enemies");
    std::fputs(",\"enemyBrains\":{",trace);
    bool comma=false;
    for(unsigned j=0;j<6;++j) {
        if(!live[j]) continue;
        PhysPt a=dsbase+enemy_ptrs[j];
        uint32_t state=rd(a+ld_state), base=rd(code+0x315d9);
        if(state<base || (state-base)%28 || (state-base)/28>=967) fail("invalid state pointer");
        uint32_t target=rd(a+ld_target); int identity=-1;
        if(target) {
            if(target==ptr) identity=0;
            else for(unsigned k=0;k<6;++k) if(target==enemy_ptrs[k]) identity=ld_enemy_ids[k]+1;
            if(identity<0) fail("target outside original enemy profile");
        }
        std::fprintf(trace,"%s\"%d\":{\"state\":%u,\"tics\":%d,\"angle\":%u,\"movedir\":%d,\"movecount\":%d,\"reaction\":%d,\"threshold\":%d,\"lastlook\":%d,\"target\":%d,\"behaviorFlags\":%u",comma?",":"",ld_enemy_ids[j],(state-base)/28,(int32_t)rd(a+ld_tics),rd(a+ld_angle),(int32_t)rd(a+ld_movedir),(int32_t)rd(a+ld_movecount),(int32_t)rd(a+ld_reaction),(int32_t)rd(a+ld_threshold),(int32_t)rd(a+ld_lastlook),identity,rd(a+ld_behaviorFlags)&224);
        std::fprintf(trace,",\"x\":%d,\"y\":%d,\"z\":%d,\"momx\":%d,\"momy\":%d,\"momz\":%d,\"health\":%d}",(int32_t)rd(a+ld_x),(int32_t)rd(a+ld_y),(int32_t)rd(a+ld_z),(int32_t)rd(a+ld_momx),(int32_t)rd(a+ld_momy),(int32_t)rd(a+ld_momz),(int32_t)rd(a+ld_health));
        comma=true;
    }
    std::fputs("},\"projectiles\":[",trace);
    for(unsigned j=0;j<shot_count;++j) {
        PhysPt a=dsbase+shot_ptrs[j];
        unsigned state=stateId(rd(a+ld_projectile_state));
        if(state<ld_shot_first_state || state>ld_shot_last_state) fail("invalid imp fireball state");
        uint32_t source=rd(a+ld_projectile_source); int identity=-1;
        if(source) {
            if(source==ptr) identity=0;
            else for(unsigned k=0;k<6;++k) if(source==enemy_ptrs[k]) identity=ld_enemy_ids[k]+1;
            if(identity<0) fail("projectile source outside original enemy profile");
        }
        std::fprintf(trace,"%s{\"x\":%d,\"y\":%d,\"z\":%d,\"momx\":%d,\"momy\":%d,\"momz\":%d,\"angle\":%u,\"floor\":%d,\"ceiling\":%d,\"state\":%u,\"tics\":%d,\"source\":%d,\"lastlook\":%d,\"missile\":%u}",
            j?",":"",(int32_t)rd(a+ld_projectile_x),(int32_t)rd(a+ld_projectile_y),(int32_t)rd(a+ld_projectile_z),
            (int32_t)rd(a+ld_projectile_momx),(int32_t)rd(a+ld_projectile_momy),(int32_t)rd(a+ld_projectile_momz),
            rd(a+ld_projectile_angle),(int32_t)rd(a+ld_projectile_floor),(int32_t)rd(a+ld_projectile_ceiling),
            state,(int32_t)rd(a+ld_projectile_tics),identity,(int32_t)rd(a+ld_projectile_lastlook),
            (rd(a+ld_projectile_flags)&ld_shot_missile_mask)?1u:0u);
    }
    std::fprintf(trace,"],\"exitRequested\":%s}}\n",action==6?"true":"false");
    if(std::fflush(trace) || std::ferror(trace)) fail("trace write failed");
    if(tick==limit) { if(std::fclose(trace)) fail("trace close failed"); std::exit(0); }
}
