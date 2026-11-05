import SSCFLP_MH36 as d
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
capa=0
mthd=2
rlevel=0 #min max expect
failrate=0.1
q=2
r=2
maxR=1.0
maxloops=50
maxloops2=200

if len(sys.argv) >= 2:
    fn=sys.argv[1]
if len(sys.argv) >= 3:
    filetype=int(sys.argv[2])
if len(sys.argv) >= 4:
    q=int(sys.argv[3])
if len(sys.argv) >= 5:
    r=int(sys.argv[4])
if len(sys.argv) >= 6:
    psize=int(sys.argv[5])
if len(sys.argv) >= 7:
    maxloops=int(sys.argv[6])
if len(sys.argv) >= 8:
    maxloops2=int(sys.argv[7])


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
   
print "CPU_time for file read and cost calculation:",time.time()-t0

obj=0.0
for i in range(d.num_units):
    k=d.NearFacilityList[i][0]
    obj+=d.nodedik[i][k]
print "original obj", obj

d.mip_solver=d.mip_solvers[0]
d.solver_message=0
sol,sols=d.RIMF_Exch_ILS(q,r,psize,maxloops,maxloops2)
print "==============solutions===================="
print "search solutions",sol
#for x in sols:
#    print x
print "final step to verify solutions...."
best_sol2=[1.0e10,[],[]]
tabu=[]
for x in sols:
    #if d.num_units>=2000: break 
    if x[0]>best_sol2[0]-0.00001:
        break
    if x[1] in tabu: continue
    obj,rlist=d.RIM_2nd_model(r,x[1],x[2],tlimit,1.0e-10)
    tabu.append(x[1][:])
    if obj<best_sol2[0]:	
		best_sol2[0]=obj	
		best_sol2[1]=x[1][:]
		best_sol2[2]=rlist[:]	
    print "best",best_sol2,"current",x[0],"->",[obj, x[1], rlist]
if d.num_units<1000: 
    print "final solution:",best_sol2[0],best_sol2[1],best_sol2[2]
print "CPU_time",time.time()-t0
