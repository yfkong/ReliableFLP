import SSCFLP_MH36 as d
import time,sys,random,math,itertools
nf=0
mincap=0
max_fcost=0.0
avg_dis=1.0
alpha=1.0
psize=5 #population size
maxloops=100 #max_loops_solution_not_improved
tlimit=7200 #timelimit for searching
filetype=0
capa=0
mthd=2
rlevel=0 #min max expect
failrate=0.1
q=3
r=3
minr=3
LB=0.0
UB=1.0e10

if len(sys.argv) >= 2:
	fn=sys.argv[1]
if len(sys.argv) >= 3:
	filetype=int(sys.argv[2])
if len(sys.argv) >= 4:
	q=int(sys.argv[3])
if len(sys.argv) >= 5:
	r=int(sys.argv[4])
if len(sys.argv) >= 6:
	LB=float(sys.argv[5])
if len(sys.argv) >= 7:
	UB=float(sys.argv[6])


fn2="na"
t0=time.time()
if filetype==0: #geo
	d.readfile(fn,fn2) #read self-defined instances
if filetype==1: # CPMP or FLP instances
	d.read_cpmp_file(fn)
if filetype==2: #pmed instances
	d.read_pmp_or_instance(fn)
if filetype==3: #tbed instances     
	d.read_bm_instance2(fn) #read tbed instances
if filetype==4: #or-lib,holmberge,yang instance
	d.read_bm_instance(fn) 
if filetype==5: #demand file f_ and supply file f2
	fn1=fn+"_demand.txt"
	fn2=fn+"_supply.txt"
	d.readfile_ab(fn1,fn2,"")
if filetype==6: #areal units f1 and connectivity file f2
	fn2=fn[:-4]+"_conn.txt"
	d.readfile(fn,fn2)

d.mip_solver=d.mip_solvers[0]
d.solver_message=0
d.print_searching_info=01
if len(sys.argv) < 7:
    sol,sols=d.RIMF_exch_search(q,r,50,100)
    best_sol=[1.0e10,[],[]]
    if sols ==[]:
        best_sol=sol
    tabu=[]
    for x in sols:
        if x[0]>best_sol[0]:
            break
        if x[1] in tabu: continue
        obj,rlist=d.RIM_2nd_model(r,x[1],x[2],tlimit,1.0e-10)
        tabu.append(x[1][:])
        if obj<best_sol[0]:	
            best_sol[0]=obj	
            best_sol[1]=x[1][:]
            best_sol[2]=rlist[:]	
        print "Best UB=",best_sol
    UB=best_sol[0]*1.00001
    LB=0.99*UB
RIM_obj,RIM_List=d.RIM_mip_model(r,tlimit,1.0e-10) 
t1=time.time()
print "UB time",time.time()-t0
LB_increased=1
attackList=[]
while 1:    
    print "-------------solving RIMF model with LB=", LB, "and UB=", UB,"--------------"
    if LB_increased==1:
        combs=itertools.combinations(range(d.num_districts),r)
        attackList=[]
        ulist=range(d.num_units)
        sol0=[d.NearFacilityList[x][0] for x in range(d.num_units)]
        obj0=sum(d.nodedik[x][sol0[x]] for x in range(d.num_units))
        cmbs=0
        for x in combs:
            cmbs+=1
            rlist=list(x)
            wd=obj0
            for j in ulist:
                k=sol0[j]
                if k not in rlist:
                    continue
                for k2 in d.NearFacilityList[j]:
                    if k2 not in rlist:
                        wd+=d.nodedik[j][k2]-d.nodedik[j][k]
                        break
            if wd<LB: continue
            attackList.append([wd,rlist])
        attackList.sort(key=lambda x:-x[0])
        print "Set K:", cmbs,"->",len(attackList),int(10*(time.time()-t0))/10.0
    t2=time.time()
    print "SetK time",time.time()-t0, time.time()-t1
    attack_K=len(attackList)
    idx_ub=attack_K
    for i in range(attack_K):
        if attackList[i][0]<LB:
            break
        idx_ub=i+1

    idx_lb=0
    for i in range(attack_K):
        if attackList[i][0]<=UB:
            break
        idx_lb=i-1
    #print "Set K:",idx_lb,attackList[idx_lb][0], attackList[idx_lb+1][0]
    sta,obj,qlist,rlist=d.IMF_BS_mip_model(q,r,RIM_List,attackList,idx_lb,idx_ub,tlimit,0.00000001)
    print [idx_lb,idx_ub],"solution:", sta,obj,qlist,rlist,int(10*(time.time()-t0))/10.0
    if sta==1: 
        break
    if sta==-2: 
        LB=UB
        UB=1.01*LB
        LB_increased=0
    if sta==-1: 
        UB=LB
        LB=0.99*UB
        LB_increased=1
print "CPU_time",time.time()-t0, time.time()-t2

