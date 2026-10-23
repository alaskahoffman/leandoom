/* Read-only observations for the pinned Chocolate Doom reference.
 * Included by g_game.c. Observer bookkeeping never modifies engine state.
 * SPDX-License-Identifier: GPL-2.0-or-later
 */
#include <stdio.h>
#include "p_local.h"
#include "r_state.h"

int LTraceMapIndex = -1;
static mobj_t *ltrace_map[10000];
static FILE *ltrace_file;
static int ltrace_tick;
extern int prndindex;

void LTraceSpawn(mobj_t *mo)
{
    if (!getenv("LEANDOOM_TRACE") || LTraceMapIndex < 0) return;
    if (LTraceMapIndex >= 10000) I_Error("trace: map object limit");
    ltrace_map[LTraceMapIndex] = mo;
}

void LTraceRemove(mobj_t *mo)
{
    int i;
    if (!getenv("LEANDOOM_TRACE")) return;
    for (i = 0; i < 10000; ++i)
        if (ltrace_map[i] == mo) ltrace_map[i] = NULL;
}

static int LTraceIdentity(mobj_t *a)
{
    int i;
    if(!a) return -1;
    if(a==players[0].mo) return 0;
    for(i=0;i<10000;++i) if(ltrace_map[i]==a) return i+1;
    I_Error("trace: target outside original-map identity profile");
    return -1;
}

static void LTraceWrite(int initial)
{
    player_t *p = &players[0];
    mobj_t *mo = p->mo;
    int i, comma;
    thinker_t *th;
    fprintf(ltrace_file, "{\"tick\":%d,\"command\":", ltrace_tick);
    if (initial) fputs("null", ltrace_file);
    else fprintf(ltrace_file,"[%d,%d,%d,%u]", p->cmd.forwardmove,p->cmd.sidemove,p->cmd.angleturn,p->cmd.buttons);
    fprintf(ltrace_file,",\"state\":{\"levelTime\":%d,\"rng\":{\"play\":%d,\"misc\":%d},",leveltime,prndindex,rndindex);
    fprintf(ltrace_file,"\"player\":{\"x\":%d,\"y\":%d,\"z\":%d,\"momx\":%d,\"momy\":%d,\"momz\":%d,\"angle\":%u,\"floor\":%d,\"ceiling\":%d,",mo->x,mo->y,mo->z,mo->momx,mo->momy,mo->momz,mo->angle,mo->floorz,mo->ceilingz);
    fprintf(ltrace_file,"\"viewZ\":%d,\"viewHeight\":%d,\"viewDelta\":%d,\"bob\":%d,\"health\":%d,\"armor\":%d,\"armorType\":%d,",p->viewz,p->viewheight,p->deltaviewheight,p->bob,p->health,p->armorpoints,p->armortype);
    fprintf(ltrace_file,"\"ammo\":[%d,%d,%d,%d],\"readyWeapon\":%d,\"pendingWeapon\":",p->ammo[0],p->ammo[1],p->ammo[2],p->ammo[3],p->readyweapon);
    if (p->pendingweapon == wp_nochange) fputs("null",ltrace_file);
    else fprintf(ltrace_file,"%d",p->pendingweapon);
    fprintf(ltrace_file,",\"secrets\":%d},",p->secretcount);
    fprintf(ltrace_file,"\"weapon\":{\"state\":%ld,\"tics\":%d,\"x\":%d,\"y\":%d,\"flashState\":%ld,\"flashTics\":%d,\"refire\":%d,\"extraLight\":%d},",p->psprites[0].state?(long)(p->psprites[0].state-states):0,p->psprites[0].tics,p->psprites[0].sx,p->psprites[0].sy,p->psprites[1].state?(long)(p->psprites[1].state-states):0,p->psprites[1].tics,p->refire,p->extralight);
    fputs("\"sectors\":[",ltrace_file);
    for(i=0;i<numsectors;++i) fprintf(ltrace_file,"%s{\"floor\":%d,\"ceiling\":%d,\"light\":%d,\"special\":%d}",i?",":"",sectors[i].floorheight,sectors[i].ceilingheight,sectors[i].lightlevel,sectors[i].special);
    fputs("],\"lineSpecials\":[",ltrace_file);
    for(i=0;i<numlines;++i) fprintf(ltrace_file,"%s%d",i?",":"",lines[i].special);
    fputs("],\"sideOffsets\":[",ltrace_file);
    for(i=0;i<numsides;++i) fprintf(ltrace_file,"%s%d",i?",":"",sides[i].textureoffset);
    fputs("],\"actors\":{",ltrace_file);
    comma=0;
    for(i=0;i<10000;++i) {
        mobj_t *a=ltrace_map[i];
        if(!a || a->player) continue;
        fprintf(ltrace_file,"%s\"%d\":{\"kind\":%d,\"x\":%d,\"y\":%d,\"z\":%d,\"health\":%d}",comma++?",":"",i,a->info->doomednum,a->x,a->y,a->z,a->health);
    }
    fputs("},\"enemyBrains\":{",ltrace_file);
    comma=0;
    for(i=0;i<10000;++i) {
        mobj_t *a=ltrace_map[i];
        if(!a || (a->type!=MT_POSSESSED && a->type!=MT_TROOP)) continue;
        fprintf(ltrace_file,"%s\"%d\":{\"state\":%ld,\"tics\":%d,\"angle\":%u,\"movedir\":%d,\"movecount\":%d,\"reaction\":%d,\"threshold\":%d,\"lastlook\":%d,\"target\":%d,\"behaviorFlags\":%u",comma++?",":"",i,(long)(a->state-states),a->tics,a->angle,a->movedir,a->movecount,a->reactiontime,a->threshold,a->lastlook,LTraceIdentity(a->target),(unsigned)a->flags&224);
        fprintf(ltrace_file,",\"x\":%d,\"y\":%d,\"z\":%d,\"momx\":%d,\"momy\":%d,\"momz\":%d,\"health\":%d}",a->x,a->y,a->z,a->momx,a->momy,a->momz,a->health);
    }
    fputs("},\"impacts\":[",ltrace_file);
    comma=0;
    /* Walk the existing thinker list read-only, preserving creation order.
     * Removed thinkers have a different callback and are skipped. */
    for(th=thinkercap.next;th!=&thinkercap;th=th->next) {
        mobj_t *a;
        if(th->function.acp1 != (actionf_p1)P_MobjThinker) continue;
        a=(mobj_t *)th;
        if(a->type != MT_PUFF && a->type != MT_BLOOD) continue;
        fprintf(ltrace_file,"%s{\"x\":%d,\"y\":%d,\"z\":%d,\"momz\":%d,\"floor\":%d,\"ceiling\":%d,\"state\":%ld,\"tics\":%d,\"lastlook\":%d}",comma++?",":"",a->x,a->y,a->z,a->momz,a->floorz,a->ceilingz,(long)(a->state-states),a->tics,a->lastlook);
    }
    fputs("],\"projectiles\":[",ltrace_file);
    comma=0;
    for(th=thinkercap.next;th!=&thinkercap;th=th->next) {
        mobj_t *a;
        if(th->function.acp1 != (actionf_p1)P_MobjThinker) continue;
        a=(mobj_t *)th;
        /* Keep exploding fireballs: P_ExplodeMissile clears MF_MISSILE. */
        if(a->type != MT_TROOPSHOT) continue;
        fprintf(ltrace_file,"%s{\"x\":%d,\"y\":%d,\"z\":%d,\"momx\":%d,\"momy\":%d,\"momz\":%d,\"angle\":%u,\"floor\":%d,\"ceiling\":%d,\"state\":%ld,\"tics\":%d,\"source\":%d,\"lastlook\":%d,\"missile\":%d}",comma++?",":"",a->x,a->y,a->z,a->momx,a->momy,a->momz,a->angle,a->floorz,a->ceilingz,(long)(a->state-states),a->tics,LTraceIdentity(a->target),a->lastlook,!!(a->flags&MF_MISSILE));
    }
    fprintf(ltrace_file,"],\"exitRequested\":%s},\"diagnostics\":{\"mapActorStates\":{",gameaction==ga_completed?"true":"false");
    comma=0;
    for(i=0;i<10000;++i) {
        mobj_t *a=ltrace_map[i];
        if(!a || a->player) continue;
        fprintf(ltrace_file,"%s\"%d\":{\"state\":%ld,\"tics\":%d,\"flags\":%u}",comma++?",":"",i,(long)(a->state-states),a->tics,(unsigned)a->flags);
    }
    fputs("}}}\n",ltrace_file);
    if (fflush(ltrace_file) || ferror(ltrace_file)) I_Error("trace: write failed");
}

static void LTraceBefore(void)
{
    const char *path=getenv("LEANDOOM_TRACE");
    if (!path || ltrace_file) return;
    ltrace_file=fopen(path,"w");
    if (!ltrace_file) I_Error("trace: cannot open output");
    LTraceWrite(1);
}

static void LTraceAfter(void)
{
    const char *limit;
    if (!ltrace_file) return;
    ++ltrace_tick;
    LTraceWrite(0);
    limit=getenv("LEANDOOM_TRACE_TICS");
    if (gameaction==ga_completed && limit && ltrace_tick < atoi(limit))
        I_Error("trace: intermission beyond exit request unsupported");
    if (!limit || ltrace_tick >= atoi(limit)) {
        if (fclose(ltrace_file)) I_Error("trace: close failed");
        exit(0);
    }
}
