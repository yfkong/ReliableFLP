import uncertainFLP03 as d
import time,sys,random,math,copy
nf=0
capa=0
maxR2=10000
maxR=10000
cover_pecentage=0
tlimit=7200 #timelimit for searching
if len(sys.argv) >= 2:
    fn1=sys.argv[1]
if len(sys.argv) >= 3:
    fn2=sys.argv[2]
if len(sys.argv) >= 4:
    nf=int(sys.argv[3])
if len(sys.argv) >= 5:
    capa=int(sys.argv[4])
if len(sys.argv) >= 6:
    maxR2=float(sys.argv[5])
if len(sys.argv) >= 7:
    maxR=float(sys.argv[6])
if len(sys.argv) >= 8:
    cover_pecentage=int(sys.argv[7])
t0=time.time()
print "reading instance data..."
K,KSet,Kp,fnodes=d.readUncertainFlpFile(fn1,fn2) #ab
print "daily average demand",d.total_pop
print "daily demands",[sum(x) for x in KSet]

d.location_problem=1
if nf>0:
    d.fixed_cost_obj=0
    d.max_num_facility=nf
    d.adaptive_number_of_facilities=0
d.heuristic_time_limit=tlimit
d.cflp_max_service_radius=maxR2
d.cflp_service_radius_preference=maxR
d.cflp_min_service_coverage_percentage=cover_pecentage

gap=0.0000000005
d.solver_message=01
#d.robust_CFLP2_Kset_mip(KSet,1,Kp,tlimit,gap)
if capa==2:
    print "solving location and size problem ..."
    d.cflpr_size_model(maxR2,maxR,cover_pecentage,nf,tlimit,gap)
if capa==1:
    d.cflpr_model(maxR2,maxR,cover_pecentage,nf,tlimit,gap)
if capa==0:
    d.uflp_model(maxR2,maxR,cover_pecentage,tlimit,gap)
    gap=0.001
    d.size_problem_Kset_mip([[d.nodes[x][3] for x in range(d.num_units)]],tlimit,gap)
for i in range(d.num_units):
        if d.nodes[i][3] == 0:
            for j in d.NearFacilityList[i]:
                if d.centersID[j]>=0:
                    #print "reassign",i,d.node_groups[i],"->",j,sum(KSet[k][i] for k in range(K))
                    d.node_groups[i]=j
                    break
centers=[x for x in range(d.num_districts) if d.centersID[x]>=0]
for i in centers: fnodes[i][-1]=1
for i in range(d.num_units):
    k=d.node_groups[i]
    d.nodes[i][-1]=k
print "selected facilities",[x for x in d.centersID if x>=0]
d.facilityCost=[x[3] for x in d.fnodes]
d.facilityCapacity=[x[4] for x in d.fnodes]
d.update_district_info()
s=str(maxR2)+"_"+str(maxR)+""+str(cover_pecentage)
fn=fn1+"_dccflp_sol"+s+".txt"
if capa==2:fn=fn1+"_dccflsp_sol"+s+".txt"
d.save_demand_file(d.nodes,fn)
print "save assignment solution in file:",fn
fn=fn2+"_dcflp_sol"+s+".txt"
if capa==2:fn=fn2+"_dcflp_sol"+s+".txt"

d.save_facility_file(fnodes,fn)
print "save site selection solution in file:",fn

sol=d.sol_stat()
print ("=========================Objectives=========================")
for x in sol:
        print(x+": "+str(sol[x]))
total_travel_cost=0.0
for k in range(K):
    travel_cost=sum(KSet[k][x]*d.nodedij[x][d.node_groups[x]] for x in range(d.num_units))
    total_travel_cost+=travel_cost*Kp[k]
print ("total_travel_cost"+str(total_travel_cost))
print "=============facility statistics======================"
print "kID, fID, Capa, NumD, Demand"
centers=[x for x in range(d.num_districts) if d.centersID[x]>=0]
overload=0.0
for i in centers:
    ulist=[x for x in range(d.num_units) if d.node_groups[x]==i]
    ol=max(0, sum(d.nodes[x][3] for x in ulist)-d.facilityCapacity[i])
    print "A",i,d.facilityCapacity[i], len(ulist), sum(d.nodes[x][3] for x in ulist),ol
    overload+=ol
print "demand:",sum(x[3] for x in d.nodes),"supply:",d.objective_supply,"overload:",overload

total_overload=0.0
for k in range(K):
    print ("--------------------------------")
    overload=0.0
    for i in centers:
        ulist=[x for x in range(d.num_units) if d.node_groups[x]==i]
        ol=max(0, sum(KSet[k][x] for x in ulist)-d.facilityCapacity[i])
        overload+=ol
        print ([k,i,d.facilityCapacity[i], len(ulist), sum(KSet[k][x] for x in ulist),ol])
    print (["demand:",sum(KSet[k]),"supply:",d.objective_supply,"overload:",overload])
    total_overload+=overload*Kp[k]
print ("--------------------------------")
print ("total_overload",total_overload)




print "=============Scenario statistics======================"
centers=[x for x in range(d.num_districts) if d.centersID[x]>=0]
fcost=sum(d.facilityCost[x] for x in centers)
dcost=0.0
for i in range(d.num_units):
    j=d.node_groups[i]
    dcost+=d.nodedik[i][j]
print "Averaged costs",fcost,dcost,fcost+dcost
for k in range(K):
    dcost=0.0
    for i in range(d.num_units):
        j=d.node_groups[i]
        dcost+=d.nodedij[i][j]*KSet[k][i]
    print "Scene",k,"cost:",fcost,dcost,fcost+dcost,"weight:", Kp[k]
print "=============ocvering statistics======================"
dlist=[25,50,75,100]
print "everage covering:",
d.coverage_stat_hems(dlist,[x[3] for x in d.nodes])
for k in range(K):
    print "scene", k, "covering:",
    d.coverage_stat_hems(dlist,KSet[k])

print ("CPU_time: "+str(time.time()-t0))