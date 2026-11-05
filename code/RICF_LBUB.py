import SSCFLP_MH36 as d
import time,sys,random,math
import itertools
nf=0
tlimit=7200 #timelimit for searching
filetype=0
q=3
r=3
maxR=1.0
r0=2
objLB=0
objUB=1.0e10
muitistart=1
if len(sys.argv) >= 2:
	fn=sys.argv[1]
if len(sys.argv) >= 3:
	filetype=int(sys.argv[2])
if len(sys.argv) >= 4:
	q=int(sys.argv[3])
if len(sys.argv) >= 5:
	r=int(sys.argv[4])
if len(sys.argv) >= 6:
	maxR=float(sys.argv[5])
if len(sys.argv) >= 7:
	objLB=int(sys.argv[6])
if len(sys.argv) >= 8:
	objUB=int(sys.argv[7])

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

d.mip_solver=d.mip_solvers[0]
d.solver_message=0
d.print_searching_info=0

Nj=[]
Ni=[[] for x in range(d.num_districts)]
for j in range(d.num_units):
	ilist=[]
	for k in range(d.num_districts):
		if d.nodedij[j][k]<=maxR:
			ilist.append(k)
			Ni[k].append(j)
	Nj.append(ilist)
Cj=[len(Nj[x]) for x in range(d.num_units)]

'''
t0=time.time()
sta, obj, qlist,rlist=d.RICF_mip_model(q,r,maxR,objLB,objUB,tlimit,0.0000005)
sol=[sta, obj, qlist,rlist]
print "RICF-LBUB",sol,time.time()-t0

t0=time.time()
sta, obj, qlist,rlist=d.RICF_MC_mip_model(q,r,maxR,objLB,objUB,tlimit,0.0000005)
sol=[sta, obj, qlist,rlist]
print "RICF-MC-LBUB",sol,time.time()-t0'''

t0=time.time()
impList=[1 for x in range(d.num_districts)]
if objLB==0:
	objLB=0.0
	for start in range(muitistart):
		sol=d.RICF_2stage(q,r,maxR,100)
		print "start",start,"heuristic solution", sol
		if sol[0]>objLB:
			objLB=sol[0]
			objUB=int(1.01*objLB)
			#impList=sol[3][:]
UB_increased=1
Klist=[]
rlists=itertools.combinations(range(d.num_districts),r)

sol=[]
while 1:
	if UB_increased==1:
		rlists=itertools.combinations(range(d.num_districts),r)
		comb=0
		Klist=[]
		for x in rlists:
			comb+=1
			rlist=list(x)
			Cj2=Cj[:]
			for k in rlist:
				for j in Ni[k]:
					Cj2[j]-=1
			covered=sum(d.nodes[x][3] for x in range(d.num_units) if Cj2[x]>0)
			if covered > objUB: continue 
			Klist.append([covered,rlist])#print rlist
		Klist.sort(key=lambda x:x[0])
		print "Set K:",comb,"->",len(Klist),"using UB",objUB,"time:",time.time()-t0    
	RIC_list=range(d.num_districts)
	UB=len(Klist)
	UB=0
	for k in range(len(Klist)):
		if Klist[k][0]>objUB:
			continue
		UB=k+1
	if UB==0: 
		objLB=objUB
		objUB=1.01*objLB
		UB_increased=1
		continue
	sta,obj,qlist,rlist=d.RICF_BS_mip_model(q,r,maxR,Nj,impList,Klist,objLB,UB,tlimit,1.0e-10)
	sol=[sta, obj, qlist,rlist]
	print "current solution",objLB,objUB,UB,sol,"time:",time.time()-t0

	if sta==1: break
	if sta==-2: 
		objUB=objLB
		objLB=0.99*objUB
		UB_increased=0
	if sta==-1: 
		objLB=objUB
		objUB=1.01*objLB
		UB_increased=1
print "RICF-LBUB",sol,time.time()-t0

