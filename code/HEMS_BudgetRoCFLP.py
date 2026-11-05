import uncertainFLP04 as d
import time,sys,random,math,copy
nf=0
capa=0
maxR2=100000.0
maxR=100000.0
cover_pecentage=0
penalty=100000.0
tlimit=14400 #timelimit for searching
Li=0.0
problem=1
rlevel=10
if len(sys.argv) >= 2:
    fn1=sys.argv[1]
if len(sys.argv) >= 3:
    fn2=sys.argv[2]
if len(sys.argv) >= 4:
    rlevel=float(sys.argv[3])
if len(sys.argv) >= 5:
    maxR2=float(sys.argv[4])
if len(sys.argv) >= 6:
    maxR=float(sys.argv[5])
if len(sys.argv) >= 7:
    cover_pecentage=int(sys.argv[6])

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
d.cflp_max_service_radius=maxR2
d.cflp_service_radius_preference=maxR
d.cflp_min_service_coverage_percentage=cover_pecentage
d.penalty_on_demand=penalty

gap=0.000000005
d.solver_message=01


urate=[d.nodes[x][4]/d.nodes[x][3] for x in range(d.num_units)]
print "urate",urate
d.heuristic_time_limit=3600

d.solver_message=0
d.RobustCEECFLP_MH(urate, rlevel, 1, 5)
d.solver_message=1
d.robustCFLP_mip(urate,rlevel,tlimit,0.0000001)


for i in range(d.num_units):
        if d.nodes[i][3] < 0.000001:
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
fn=fn1+"_BRO_sol"+str(int(d.objective))+".txt"
d.save_demand_file(d.nodes,fn)
print "save assignment solution in file:",fn
fn=fn2+"_BRO_sol"+str(int(d.objective))+".txt"
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
print "total_travel_cost",total_travel_cost

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
    print "--------------------------------"
    overload=0.0
    for i in centers:
        ulist=[x for x in range(d.num_units) if d.node_groups[x]==i]
        ol=max(0, sum(KSet[k][x] for x in ulist)-d.facilityCapacity[i])
        overload+=ol
        print k,i,d.facilityCapacity[i], len(ulist), sum(KSet[k][x] for x in ulist),ol
    print "demand:",sum(KSet[k]),"supply:",d.objective_supply,"overload:",overload
    total_overload+=overload*Kp[k]
print "--------------------------------"
print "total_overload",total_overload

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