import SOCP_solver3 as d
import Metrix_decom as decom
import time,sys,random,math
nf=0
mincap=0
max_fcost=0.0
avg_dis=1.0
alpha=1.0
psize=5 #population size
maxloops=100 #max_loops_solution_not_improved
tlimit=7200 #timelimit for searching
filetype=0
capa=1
mthd=2
rlevel=0.0
seed=1
problem=0
maxR2=10000.0
maxR=10000.0
cover_pecentage=0
penalty=100.0
if len(sys.argv) >= 2:
    fn1=sys.argv[1]
if len(sys.argv) >= 3:
    fn2=sys.argv[2]
if len(sys.argv) >= 4:
    problem=int(sys.argv[3])
if len(sys.argv) >= 5:
    rlevel=float(sys.argv[4])
if len(sys.argv) >= 6:
    maxR2=float(sys.argv[5])
if len(sys.argv) >= 7:
    maxR=float(sys.argv[6])
if len(sys.argv) >= 8:
    cover_pecentage=int(sys.argv[7])
    
d.distance_type=0
t0=time.time()
print ("reading instance data...")
K,KSet,Kp,fnodes=d.readUncertainFlpFile(fn1,fn2) #ab
#print "daily average demand",d.total_pop
print ("daily demands"+str([sum(x) for x in KSet]))
 
d.heuristic_time_limit=tlimit
d.cflp_max_service_radius=maxR2
d.cflp_service_radius_preference=maxR
d.cflp_min_service_coverage_percentage=cover_pecentage
d.penalty_on_demand=penalty
d.solver_message=1
print("==========================solving==========================")

#d.CFLP_SOCP_mip(sigma,rlevel,tlimit,0.0000000005)
if problem==0:
    d.CFLP_SOCP_mip([x[4] for x in d.nodes],rlevel,tlimit,0.000000005)
if problem==1:
    d.CFLSP_SOCP_mip([x[4] for x in d.nodes],rlevel,tlimit,0.000000005)

#d.RoCFLP_L2_SOCP_mip(matrixL,gama,tlimit,0.000000005)
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
print ("selected facilities"+str ([x for x in d.centersID if x>=0]))
d.facilityCost=[x[3] for x in d.fnodes]
d.facilityCapacity=[x[4] for x in d.fnodes]
d.update_district_info()
s=str(maxR2)+"_"+str(maxR)+""+str(cover_pecentage)
fn=fn1+"_RoCFLPL2_sol"+s+".txt"
if capa==1:fn=fn1+"_RoCFLSPL2_sol"+s+".txt"
d.save_demand_file(d.nodes,fn)
print ("save assignment solution in file:"+str(fn))
fn=fn2+"_RoCFLPL2_sol"+str(int(d.objective))+".txt"
if capa==1:fn=fn2+"_RoCFLSPL2_sol"+s+".txt"
d.save_facility_file(fnodes,fn)
print ("save site selection solution in file:"+str(fn))

sol=d.sol_stat()
print ("=========================Objectives=========================")
for x in sol:
        print(x+": "+str(sol[x]))
total_travel_cost=0.0
for k in range(K):
    travel_cost=sum(KSet[k][x]*d.nodedij[x][d.node_groups[x]] for x in range(d.num_units))
    total_travel_cost+=travel_cost*Kp[k]
print ("total_travel_cost:"+str(total_travel_cost))

print ("=============facility statistics======================")
print ("kID, fID, Capa, NumD, Demand")
centers=[x for x in range(d.num_districts) if d.centersID[x]>=0]
overload=0.0
for i in centers:
    ulist=[x for x in range(d.num_units) if d.node_groups[x]==i]
    ol=max(0, sum(d.nodes[x][3] for x in ulist)-d.facilityCapacity[i])
    s= "A "+str([i,d.facilityCapacity[i], len(ulist), sum(d.nodes[x][3] for x in ulist),ol])
    print(s)
    overload+=ol
print(["demand:",sum(x[3] for x in d.nodes),"supply:",d.objective_supply,"overload:",overload])
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

print ("=============Scenario statistics======================")
centers=[x for x in range(d.num_districts) if d.centersID[x]>=0]
fcost=sum(d.facilityCost[x] for x in centers)
dcost=0.0
for i in range(d.num_units):
    j=d.node_groups[i]
    dcost+=d.nodedik[i][j]
print (["Averaged costs",fcost,dcost,fcost+dcost])
for k in range(K):
    dcost=0.0
    for i in range(d.num_units):
        j=d.node_groups[i]
        dcost+=d.nodedij[i][j]*KSet[k][i]
    print ("Scene",k,"cost:",fcost,dcost,fcost+dcost,"weight:", Kp[k])
print ("=============ocvering statistics======================")
dlist=[25,50,75,100]
print ("everage covering:")
d.coverage_stat_hems(dlist,[x[3] for x in d.nodes])
for k in range(K):
    print ("scene"+str(k)+"covering:")
    d.coverage_stat_hems(dlist,KSet[k])
print ("CPU_time: "+str(time.time()-t0))