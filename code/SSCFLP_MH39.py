# -*- coding: utf-8 -*-
## An unified algorithm framework for the Facility Location, Allocation, Service Area, and Regionalization Problems. 
## yfkong@henu.edu.cn, Dec.,2024
## to solve problems using MIP solvers and/or heuristic algorithms:
## 1 TP, GAP, SAP, EAP
## 2 SSCFLP, SSCKFLP, CFLSAP, CKFLSAP
## 3 PMP/CPMP
## 4 PCP
## 5 EDP,EFLSAP
## 6 DCCFLP - CFLP with maximum covering radius and covering percentage
## 7 extended PMP, CPMP with inequity inverse objective
## 8 extended UFLP, CFLP with cost-efficienc and equitable objective
## 9 uncapaitiated and capacitated PCP, k-centrum, alpha-centdian, k-centdian problems, FFLP(extended FFLP,Filippi et al. 2021)
## 10 MinSD, MinMAD, MinAD, MinCV, MinSI, MinGC location problems
## 11 Regionalization problem using multi-attibutes with atribute weights and areal weights
## 12 2SFCA, 2SOpt
## 13 EDELP, CEDELP,BEDELP,CBEDELP
## 14 gama-RobustCFLP, RobustCBFLP, RobustBEECFLP
## 15 DR-RUFLP,DR-RCFLP,DR-RBFLP,DR-RBCFLP
## 16 ReliableSCLP,ReliableCSCLP,ReliableMCLP, ReliableBMCLP, ReliableCMCLP, ReliableBCMCLP
## 17 ProtectedSCLP,ProtectedCSCLP,ProtectedMCLP,ProtectedBMCLP,ProtectedCMCLP,ProtectedBCMCLP
## 18 alpha-Reliable beta-service level UFLP & CFLP

import sys,os,random,time,copy,math,tempfile, keyboard
import itertools
#from gurobipy import GRB_Model, GRB
#mip solver
mip_solvers=[] #MIP solvers supported 
mip_solver=''  #MIP solver, "cplex", "cbc" or ""
mip_file_path=tempfile.gettempdir()
os.chdir(mip_file_path)  #used in arcgis
try:
	import pulp
	s=pulp.apis.GUROBI_CMD()
	if s.available()==False:
		pass
	else:
		mip_solvers.append('gurobi')
	s=pulp.apis.cplex_api.CPLEX_CMD()
	if s.available()==False:
		pass
	else:
		mip_solvers.append('cplex')
	s=pulp.apis.COIN_CMD()
	if s.available()==False:
		pass
	else:
		mip_solvers.append('cbc')
except: 
	pass
if len(mip_solvers)>0: mip_solver=mip_solvers[0]

#constant
MAXNUMBER=1.0e+20
MINNUMBER=1.0e-20
bigM=100000.0

#instance info
nodes=[]
nodes_std=[] #for homoDP only
weight_features=[] #for homoDP only
num_units=-1
nodedij=[]
nodedik=[]  #weighted cost from i to k, =nodedij*nodes[][3] 
nodendij=[] #network distance
node_neighbors=[]
facility_neighbors=[]
total_pop=0
avg_pop=0
total_supply=0
distance_type=0 #0 Euclidean, 1 Manhattan, 2 Geo, 3 Network
distance_meter2kilimeter=1
all_units_as_candadate_locations=0
facilityCandidate=[] #attribute = 0,1,2...
facility_inclusion_list=[] #attribute = 1
facilityCapacity=[]
facilityMinimumCapacity=0
facilityMaximumCapacity=0
facilityCost=[]
num_facilityCandidate=-1
num_districts=-1 # number of service areas/facilities
avg_dis_min=1.0
potential_facilities=[]
NearFacilityList=[]
nearCustomer=[]
nearCustomers=[]

#problem parameters
location_problem=1
max_num_facility=0
max_facility_cost=0
max_num_reserved_facility=0
adaptive_number_of_facilities=1
fixed_cost_obj=1
travel_distance_weight=1
spatial_contiguity=1 # 0 no, 1 yes, 2 yes with multi-parts
spatial_contiguity_minimum_percentage=5
penalty_on_demand=100000.0
pop_deviation=0.00 #for pdp, 5%
cflp_max_service_radius=100000.0
cflp_service_radius_preference=100000.0
cflp_min_service_coverage_percentage=0.0
envy_service_distance=100000.0
#travel_distance_weight=1 #pmp only
envy_service_objective=0 
#0: no envy; 
#1: envy obj with weight; 
#4: envy(abs_dev) obj with weight; 
envy_objective_weight_of_travelcost=1.0
envy_objective_weight=0.0
mean_distance_epsilon=0.01    #ϵ-constrained method

#current solution
centersID=[]
node_groups=[]
district_info=[] #[[0,0,0.0] for x in range(num_districts)] # solution
objective_overload=0
obj_balance=MAXNUMBER
objective=MAXNUMBER
objective_fcost=0.0
biobjective=MAXNUMBER
objective_supply=0.0
objective_envy=0.0
objective_covered=0
objective_rmax_not_covered=0
objective_pentalty_on_overload=0.0
objective_pentalty_on_rmax=0.0
objective_pentalty_on_covering=0.0
given_solution=0 #reserved
all_solutions=[]

#best solution in each start
best_solution =[] # node_groups[:]
best_centersID=[]
best_biobjective=MAXNUMBER
best_objective=MAXNUMBER
best_objective_overload = MAXNUMBER
best_objective_fcost = 0.0
#global best solution 
#best_centers_global=[]
best_solution_global=[]
best_centersID_global=[]
best_biobjective_global = MAXNUMBER
best_objective_global = MAXNUMBER
best_objective_fcost_global = 0.0
best_overload_global = MAXNUMBER

#search statistics
time_check=0
time_check_edge_unit=0
time_spp=0.0
time_update_centers=0.0
time_op=[0.0 for x in range(10)]
time_ruin_recreate=[0.0 for x in range(10)]
time_location=[0.0 for x in range(10)]
time_pmp_re_location=0.0
time_Whitaker=0.0
time_LNS1=0.0
time_LNS2=0.0
time_repair=0
count_op=[0.0 for x in range(10)]
check_count=0
improved=0
move_count=0

#search histry
region_pool = []
pool_index=[]

#local search
acceptanceRule="hc" #solver name
assignment_operators_selected=[0,1] #0 one-unit move, 1 two-unit move, 2 three-unit move
location_operators_selected=[0,1,2,3,4] #0 swap, 1 drop, 2 add, 3 add+drop, 4 me
ruin_oprators=[0,1,2,3,4] #ruin0, ruin1, 9 mip assign
sub_model_neigborhood_types=[0] #0-circle, 1-corridor, 2-large-circle,3-very large circle with 30 faiclity
large_neigborhood_maxIJ=10000 #MaxIJ=4000, 6000, 8000, 10000
multi_start_count=6 #population size for GA, ILS, VNS, LIS+VND
initial_solution_method=0 #0 construction, 1 LP
init_methods=[0,1]
assign_method=0 #not used
large_facility_cost=0
maxloops=1000
max_loops_solution_not_improved=-1
SA_maxloops = 100 # maximum number of search loops for GA
SA_temperature=1.0
op_random = 1 # operators used sequentially (0) or randomly(1)
last_loop_obj=0.0
ruin_percentage=20
mainloop=0
mutation_rate=0.01 
cross_methods=-1
solution_similarity_limit=10.0

#mip modelling for inititail solution, spp and full model
is_spp_modeling=1 #0 no spp modelling, 1 modelling at the end, 2 modelling in case of local optimum
linear_relaxation=0
spp_loops=400
solver_time_limit=7200 #used for mip modeling
solver_mipgap=0.000000000001
solver_message=0
heuristic_time_limit=7200

seed =random.randint(0,10000)
random.seed(seed)

print_searching_info=1
stop_searching=0
def on_key_event(e):
	global stop_searching
	#print e.name    
	if e.name=="esc":
		stop_searching=1    
		print "\nuser break...!"
keyboard.on_press_key('esc', on_key_event)

def arcpy_print(s):
	if print_searching_info==0:
		return
	print s

#record a region in current solution
def update_region_pool(rid):
	global pool_index
	global time_spp
	global region_pool
	t=time.time()
	if is_spp_modeling<=0: return
	if facilityMaximumCapacity>0 and  district_info[rid][1]>facilityMaximumCapacity: return
	if facilityMinimumCapacity>0 and  district_info[rid][1]<facilityMinimumCapacity: return
	if centersID[rid]<0: return
	#if spatial_contiguity==1 and check_continuality_feasibility(node_groups,rid)<1:
	#    return
	ulist=[x for x in  range(num_units) if node_groups[x]==rid]
	if ulist==[]:
		#print "empty area:",rid,node_groups
		return
	cost1=district_info[rid][2]
	cost2=sum(nodedik[x][rid] for x in ulist)
	if location_problem==9: cost2=sum(nodedij[x][rid] for x in ulist)
	if abs(cost1-cost2)>0.001: print rid,cost1,cost2
	obj=district_info[rid][2]+district_info[rid][4]*penalty_on_demand
	idx=int(obj*1000000)
	idx+=sum((x+13)*(x+137) for x in ulist)
	if idx not in pool_index[rid]:
		pool_index[rid].append(idx)
		region_pool.append([ulist,district_info[rid][2],district_info[rid][1],district_info[rid][4],rid])
	time_spp+=time.time()-t
	return

#record all regions in current solution
def update_region_pool_all():
	if is_spp_modeling<=0:
		return
	for rid in range (num_districts):
		if centersID[rid]<0: continue
		update_region_pool(rid)
		
def delete_region_pool_all():
	global region_pool
	global pool_index
	region_pool=[]
	for i in range(num_districts):
		pool_index[i]=[]

#check continuality of a solution (sol)
def check_solution_continuality_feasibility(sol):
	#if spatial_contiguity==0: return 9
	feasible = spatial_contiguity
	for i in range (num_districts):
		if centersID[i]<0: continue
		if check_continuality_feasibility(sol,i) <= 0:
			feasible=0  #infeas.
			break
	return feasible

def check_current_solution_continuality_feasibility():
	feaslist=[]
	for i in range (num_districts):
		if centersID[i]<0: continue
		sta=check_continuality_feasibility(node_groups,i)
		feaslist.append(sta)
	return feaslist

#check continuality of a region (rid) in solution (sol)
def check_continuality_feasibility(sol,rid):
	global time_check
	global check_count
	u=facilityCandidate[rid]
	check_count+=1
	t=time.time()
	ulist1=[x for x in range(num_units) if sol[x]==rid and x!=u]
	ulist2=[u]
	#ulist2.append(ulist1.pop())
	for x in ulist2:
		for i in range(len(ulist1)):
			j=ulist1[i]
			if j in node_neighbors[x]:
				ulist2.append(j)
				ulist1[i]=-1
		ulist1=[x for x in ulist1 if x>=0]
	if len(ulist1)==0:          
		time_check+=time.time()-t
		return 1  #feasible
	if spatial_contiguity==2:
		ulist=[x for x in range(num_units) if sol[x]==rid]
		flist=frag_unit_minority(ulist,rid)
		if flist==[]: 
			time_check+=time.time()-t
			return 2
	time_check+=time.time()-t
	return 0    #infeasible

#check continuality of a list of units
def check_ulist_continuality(ulist):
	if spatial_contiguity==0: return 1
	global time_check
	global check_count
	t=time.time()
	ulist1=ulist[:]
	ulist2=[]
	ulist2.append(ulist1.pop())
	check_count+=1
	for x in ulist2:
		for i in range(len(ulist1)):
			#if ulist1[i]==-1: continue
			if ulist1[i] in node_neighbors[x]:
				ulist2.append(ulist1[i])
				ulist1[i]=-1
		ulist1=[x for x in ulist1 if x>=0]         
	#ulist3=[x for x in ulist1 if x!=-1]
	if len(ulist1)==0:          
		time_check+=time.time()-t
		return 1  #feasible
	if spatial_contiguity==2:
		k=node_groups[ulist[0]]  
		flist=frag_unit_minority(ulist,k)
		time_check+=time.time()-t
		if flist==[]: return 2
	return 0    #infeasible

#return a list of boundary units
def find_edge_units():
	if spatial_contiguity==0 and random.random()>0.5:
		return find_tail_units()
	ulist=[]
	for x in range(num_units):
		if x in centersID: continue        
		if spatial_contiguity==1 and x in centersID:
			continue  #bug for benckmark instances
		k=node_groups[x]
		for y in node_neighbors[x]:
			if node_groups[y] != k:
				ulist.append(x)
				break
	random.shuffle(ulist)
	if objective_overload==0: 
		return ulist
	ulist=[[x, district_info[node_groups[x]][4]] for x in ulist]
	ulist.sort(key=lambda x:-x[1])
	ulist=[ x[0] for x in ulist]
	return ulist

def find_tail_units():
	#p=1.0
	#nf=sum(1 for x in centersID if x>=0)
	#nu=num_units*1.0/nf
	#if nu>7:
	#    p=(4.0*math.sqrt(nu)-4)/nu
	tlist=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
		ulist=[[x,nodedij[x][k]] for x in range(num_units) if node_groups[x]==k]
		ulist.sort(key=lambda x:-x[1])
		#n=int(len(ulist)*p)
		n=len(ulist)
		if n>7: n=int(4*math.sqrt(n))-4
		if n<1: n=1
		ulist=ulist[:n]
		tlist+=[x[0] for x in ulist]
	random.shuffle(tlist)
	#return tlist 
	if objective_overload==0: #!!!
		return tlist
	#ulist=[ [x, district_info[node_groups[x]][4]] for x in tlist]
	ulist=[[x,nodedij[x][node_groups[x]]*(1+district_info[node_groups[x]][4]*10)] for x in tlist]
	ulist.sort(key=lambda x:-x[1])
	ulist=[ x[0] for x in ulist]
	#print len(tlist)
	return ulist

#return a list of edge units that having three or more neighor regions
def find_edge_units_2():
	ulist=[]
	for x in range(num_units):
		if spatial_contiguity==1 and x in centersID: continue #bug for benckmark instances
		rlist=[node_groups[y] for y in node_neighbors[x]]
		rlist.append(node_groups[x])
		rset=set(rlist)
		if len(rset)>2:
			ulist.append(x)
	random.shuffle(ulist)
	return ulist

#check an edge unit (uid), reserved
def is_edge_unit(uid):
	#global time_check_edge_unit
	if spatial_contiguity==0: return True
	t=time.time()
	rlist = [node_groups[x] for x in node_neighbors[uid]]
	rlist+=node_groups[uid]
	#time_check_edge_unit+=time.time()-t
	if len(set(rlist))==1:
		return False
	return True

#update region information of the current solution
def update_district_info():
	global objective_overload
	global objective
	global biobjective
	global objective_fcost
	global district_info
	global move_count
	#global centersID
	global objective_supply
	global avg_dis_min
	for k in range(num_districts):
		district_info[k][0] = 0
		district_info[k][1] = 0.0
		district_info[k][2] = 0.0
		district_info[k][3] = 0.0
		district_info[k][4] = 0.0
	for k in range(num_districts):
		if centersID[k]<0 and k in node_groups:
			arcpy_print("debug: a facility not selected but used: " + str(k))
			#centersID[k]=facilityCandidate[k]
	for k in range(num_districts):
		if centersID[k]<0:
			continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		if len(ulist)==0:
			if location_problem==3: continue
			'''if adaptive_number_of_facilities==1 and k not in facility_inclusion_list:
				centersID[k]=-1
				continue'''
		district_info[k][0] = len(ulist)
		district_info[k][1] = sum(nodes[x][3] for x in ulist)
		district_info[k][2] = sum(nodedik[x][k] for x in ulist)
		if location_problem==9: district_info[k][2] = sum(nodedij[x][k] for x in ulist)
		district_info[k][3] = facilityCapacity[k] 
		district_info[k][4] = max(0.0,district_info[k][1]-facilityCapacity[k]) # -district_info[k][3]
		if location_problem==3: district_info[k][4]=0 #pmp
		if location_problem==2: #pdp,edp
			bal=0.0
			dev=pop_deviation*1.0*total_pop/max_num_facility
			if district_info[k][1]>district_info[k][3]+dev: bal=district_info[k][1]-district_info[k][3]-dev
			if district_info[k][1]<district_info[k][3]-dev: bal=district_info[k][3]-district_info[k][1]-dev
			district_info[k][4]=bal
		#print centersID,node_groups
	bal=sum(x[4] for x in district_info)
	objective=sum([x[2] for x in district_info])
	objective_overload=bal
	#if objective/total_pop<avg_dis_min:
	#    avg_dis_min=objective/total_pop
	avg_dis_min=objective/total_pop
	biobjective=objective+objective_overload*penalty_on_demand

	objective_supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x] >=0)
	#biobjective=objective+objective_overload*avg_dis_min*1000000
	#biobjective=bal2*avg_dis_min*1000000
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x] >=0)
	objective_fcost=fcost
	if fixed_cost_obj==1:
		biobjective+=fcost
	move_count+=1

def find_frag_unit():
	if spatial_contiguity==0: return []
	global time_check_edge_unit
	t=time.time()    
	frag_units=[]
	if spatial_contiguity==2:
		for k in range(num_districts):
			if centersID[k]==-1: continue
			ulist=[x for x in range(num_units) if node_groups[x]==k]
			nflist=frag_unit_minority(ulist,k)
			frag_units+=nflist
	if spatial_contiguity!=2:
		for k in range(num_districts):
			if centersID[k]==-1: continue
			ulist2=[centersID[k]]
			ulist1=[x for x in range(num_units) if node_groups[x]==k and x!=centersID[k]]
			for x in ulist2:
				for i in range(len(ulist1)):
					if ulist1[i]==-1: continue
					if ulist1[i] in node_neighbors[x]:
						ulist2.append(ulist1[i])
						ulist1[i]=-1
				ulist1=[x for x in ulist1 if x>=0]
			frag_units+=ulist1

	random.shuffle(frag_units)
	time_check_edge_unit+=time.time()-t
	#print len(frag_units),
	return frag_units

def frag_unit_minority(ulist,k):
	final_list=[]
	ulist1=ulist[:]
	ulist1.remove(k)
	ulist2=[k]
	total_area=sum(x[3] for x in nodes)
	while 1:
		for x in ulist2:
			for i in range(len(ulist1)):
				if ulist1[i]==-1: continue
				if ulist1[i] in node_neighbors[x]:
					ulist2.append(ulist1[i])
					ulist1[i]=-1
			ulist1=[x for x in ulist1 if x>=0]
		final_list.append([len(ulist2),ulist2[:]])
		if len(ulist1)<=1:
		   if len(ulist1)==1:
				final_list.append([1,ulist1[:]])
		   break
		u=ulist1[0]
		ulist2=[u]
		del ulist1[0]
	if len(final_list)==1: return []
	final_list.sort(key=lambda x:x[0])
	#del final_list[-1]
	flist=[]
	n=total_area*spatial_contiguity_minimum_percentage/max_num_facility/100
	for x in final_list: 
		area=sum(nodes[i][3] for i in x[1])
		if area>n:continue
		if k in x[1]: continue        
		flist+=x[1]
	#print [len(flist),len(ulist)],
	return flist

def district_with_multiparts(ulist):
	final_list=[]
	ulist2=ulist[:1]
	ulist1=ulist[1:]
	while 1:
		for x in ulist2:
			for i in range(len(ulist1)):
				if ulist1[i]==-1: continue
				if ulist1[i] in node_neighbors[x]:
					ulist2.append(ulist1[i])
					ulist1[i]=-1
			ulist1=[x for x in ulist1 if x>=0]
		final_list.append([len(ulist2),ulist2[:]])
		if len(ulist1)<=1:
		   if len(ulist1)==1:
				final_list.append([1,ulist1[:]])
		   break
		u=ulist1[0]
		ulist2=[u]
		del ulist1[0]
	final_list.sort(key=lambda x:-x[0])
	#del final_list[-1]
	flist=[x[0] for x in final_list]
	return flist

def repair_fragmented_solution_large_instance():
	global node_groups
	global centersID
	global time_repair
	if spatial_contiguity==0: return
	t=time.time()
	frag_units=find_frag_unit()
	#print "frag_units",len(frag_units),
	if len(frag_units)==0: return
	#sol=node_groups[:]
	for x in frag_units:
		node_groups[x]=-1
	update_district_info()

	'''while len(frag_units)>0:
		cands=[]
		for x in frag_units:
			for y in node_neighbors[x]:
				k=node_groups[y]
				if k<0: continue
				cands.append([x,k,nodedik[x][k]])
		if cands==[]: break
		cands.sort(key=lambda x:x[2])
		n=len(cands)/10
		if n<1: n=1
		for x in cands[:n]:
			nid=x[0]
			if node_groups[nid]>=0: continue
			node_groups[nid]=x[1]
			if nid in frag_units: frag_units.remove(x[0])'''
	while 1:
		assigned=0
		for i in range(len(frag_units)):
			u=frag_units[i]
			for v in node_neighbors[u]:
				k=node_groups[v]
				if k>=0: 
					assigned=1
					node_groups[u]=k
					frag_units[i]=-1
					break                    
		frag_units=[x for x in frag_units if x>=0]
		if len(frag_units)==0: break
		if assigned==0: break    

	for x in frag_units:
		for k in NearFacilityList[x]:
			if centersID[k]>=0:
				 node_groups[x]=k
				 break
	#print len(frag_units)
	#print int(objective),
	update_district_info()
	#print int(objective),
	repair_fragmented_solution()
	time_repair+=time.time()-t
	#print objective,
	
#repair the fragmented solution
def repair_fragmented_solution():
	global node_groups
	global centersID
	global time_repair
	if spatial_contiguity==0: return
	nf=sum(1 for x in centersID if x>=0)
	if num_units/nf>100 and location_problem==3:
		 repair_fragmented_solution_large_instance()
		 return
	'''for k in range(num_districts):
		if centersID[k]<0: continue
		u=nearCustomer[k]
		node_groups[u]=k'''
	update_district_info()
	frag_units=find_frag_unit()
	#print "frag_units",len(frag_units),
	if len(frag_units)==0: return
	sol=node_groups[:]
	for x in frag_units:
		node_groups[x]=-1
	# if location_problem>=3:
		# for k in range(num_districts):
			# if centersID[k]<0: continue
			# if node_groups[k]>=0: continue
			# c,ulist=update_center(k)
			# centersID[k]=-1
			# centersID[c]=c
			# for x in ulist: node_groups[x]=c
	update_district_info()
	#print len(frag_units),
	while len(frag_units)>0:
		newk=-1
		nid=-1
		cost=MAXNUMBER
		for x in frag_units:
			for y in node_neighbors[x]:
				k=node_groups[y]
				if k>=0:
					gap=max(district_info[k][1]+ nodes[x][3] - facilityCapacity[k],0)
					if location_problem==3: gap=0
					cost2=gap*penalty_on_demand + nodedik[x][k]
					if cost2<cost:
						nid=x
						newk=k
						cost=cost2
		if newk>=0:
			node_groups[nid]=newk
			update_district_info()
			frag_units.remove(nid)
		else:
			break
	#print "frag_units", frag_units
	for x in frag_units:
		node_groups[x]=sol[x]
	#print len(frag_units)
	#print int(objective),
	update_district_info()
	#print check_current_solution_continuality_feasibility()
	#print int(objective),

#r&r method
#remove the edge units and reassign them to nearest facilities
def r_r_perb_edge_units():
	global node_groups
	ulist=find_edge_units() 
	num=int(len(ulist)*ruin_percentage/100)
	if num<1: num=1
	ulist=ulist[:num]
	for x in ulist:
		#if x in centersID: continue
		for k in NearFacilityList[x]:
			if centersID[k]>=0:
				node_groups[x]=k
				break
	update_district_info()
	if spatial_contiguity>=1: repair_fragmented_solution()

def r_r_large_region():
	global node_groups
	dlist=select_region(-1)
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	num=int(nf*ruin_percentage/100)
	num=max(num,3)
	num=min(num,5)
	dlist=dlist[:num]
	#if len(dlist)>3: dlist=dlist[:3]
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	for x in ulist:
		for k in NearFacilityList[x]:
			if centersID[k]>=0:
				node_groups[x]=k
				break
	update_district_info()
	if spatial_contiguity>=1: repair_fragmented_solution()

#r&r method
def r_r_perb_location():
	global node_groups
	nf =sum(1 for x in centersID if x>=0)
	ulist=find_edge_units_2()
	if len(ulist)==0:
		ulist=find_edge_units()
	if len(ulist)==0:
		return 
	ulist=[ulist[0]]
	pop=0
	num=int(num_units*ruin_percentage/100)
	#if num<2: num=2
	for x in ulist:
		for y in node_neighbors[x]:
			if y not in ulist:
				ulist.append(y)
		if len(ulist)>=num:
			break
	for x in ulist:
		for k in NearFacilityList[x]:
			if centersID[k]>=0:
				node_groups[x]=k
				break
	update_district_info()
	if spatial_contiguity>=1: repair_fragmented_solution()

def r_r_pathrelink_AP():
	global node_groups
	for i in range(num_units):
		klist=[x[2][i] for x in all_solutions]
		r=random.random()
		idx=int(r*r*0.999*len(klist))
		#idx=random.randint(0,len(klist)-1)
		k=klist[idx]
		node_groups[i]=k    
	update_district_info()
	if spatial_contiguity>=1:
		repair_fragmented_solution()

location_tabu_list=[]
def r_r_new_location(r): #add drop interchange swap/shift(add+drop) 
	global time_location
	global add_not_improved
	global location_tabu_list
	global TB_tabu_list
	if len(location_operators_selected)==0: return -1,0
	nf=sum(1 for x in centersID if x>=0)
	location_operators=location_operators_selected[:]  #[0,1,2,3,4]#[0,1,3,4]
	#minregion=min(x[1] for x district_info if x[0]>0) 
	#if 0 in location_operators and (objective_supply-total_pop)/2 < minregion: location_operators.remove(0)
	idx=r
	if idx<0:
		idx=random.randint(0,len(location_operators)-1)
		idx=location_operators[idx]
	#if adaptive_number_of_facilities==0:
	#    if 1 in location_operators: location_operators.remove(1)
	#    if 2 in location_operators: location_operators.remove(2)
	sta=-1
	t=time.time()
	if idx==0:
		sta=r_r_location_swap_greedy()
		#time_location[0]+=time.time()-t
	if idx==1: 
		sta=r_r_location_drop_greedy() 
		#time_location[1]+=time.time()-t
	if idx==2: 
		sta=r_r_location_add_greedy()
		#time_location[2]+=time.time()-t
	if idx==3: 
		sta=r_r_location_add_greedy()
		RRT_local_search()
		sta=r_r_location_drop_greedy() 
		#time_location[3]+=time.time()-t
	if idx==5: 
		sta=r_r_reselect_location_pmp()
		#time_location[5]+=time.time()-t
	if idx==6: 
		sta=pmp_TB2()
		#time_location[6]+=time.time()-t
	if idx==7: 
		sta=pmp_TB()
		#time_location[7]+=time.time()-t
	if idx==8: #mip location search 
		sta=pmp_Whitaker()
		#obj=biobjective
		#sta=MIP_PMP_location_search()
		#if biobjective>obj-0.00000001:
		#    TB_tabu_list.append(centersID)
		#time_location[8]+=time.time()-t
	if idx==9: #mip location search 
		#print check_current_solution_continuality_feasibility()
		sta=MIP_location_search()
		time_location[9]+=time.time()-t
	if spatial_contiguity>=1:
		repair_fragmented_solution()
			#print check_current_solution_continuality_feasibility()
	if centersID not in location_tabu_list:
		location_tabu_list.append(centersID[:])
	#if sta==1: VND_local_search()
	time_location[idx]+=time.time()-t
	return idx,sta
def r_r_location_add_greedy():
	global centersID
	global node_groups
	if adaptive_number_of_facilities==0: return 0
	clist=[x for x in range(num_districts) if centersID[x]<0]# and x in potential_facilities]
	if len(clist)==0: return 0
	addlist=[]
	for nk in clist:
		ids=centersID[:]
		ids[nk]=facilityCandidate[nk]
		if locations_exist(ids)==1: continue
		if ids in location_tabu_list: continue
		ulist=[[x,nodedij[x][nk]] for x in range(num_units) if nodedij[x][nk]<nodedij[x][node_groups[x]]]
		#ulist=[[x,nodedik[x][node_groups[x]]-nodedik[x][nk]] for x in range(num_units) if nodedik[x][node_groups[x]]>nodedik[x][nk]]
		ulist.sort(key=lambda x:x[1])
		savings=0.0
		if fixed_cost_obj==1: savings=-facilityCost[nk]
		ndemand=0
		nsupply=facilityCapacity[nk]
		for x,y in ulist:
			#if nk==0: print savings, 
			if ndemand+nodes[x][3]<=nsupply:
				ndemand+=nodes[x][3]
				savings+=nodedik[x][node_groups[x]]-nodedik[x][nk] #*nodes[x][3]
		#if nk==0: print "addeval", nk,savings
		if savings<-0.02*biobjective: continue
		addlist.append([nk,savings,copy.deepcopy(ulist)])
	if len(addlist)==0: return 0
	addlist.sort(key=lambda x:-x[1])
	if len(addlist)==0: return 0
	if addlist[0][1]>=0:
		while addlist[-1][1] <0:
			addlist.pop()

	#print "add", [ addlist[x][1] for x in range(min(len(addlist),5))]
	#print [ [x[0],x[1],facilityCost[x[0]]] for x in addlist]
	r=random.random()
	idx=int(r*r*0.999*min(3,len(addlist)/2))
	#idx=0
	k=addlist[idx][0]
	centersID[k]=facilityCandidate[k]
	ulist=addlist[idx][2]
	#for x,y in ulist: print "u", x, nodedij[x][node_groups[x]], nodedij[x][k],nodedik[x][node_groups[x]], nodedik[x][k],nodedik[x][node_groups[x]]-nodedik[x][k]
	#print "add", idx,k,addlist[idx][1]
	ndemand=0
	nsupply=facilityCapacity[k]
	if spatial_contiguity>=1:
		u=nearCustomer[k]
		node_groups[u]=k
		ndemand+=nodes[u][3]
	for x,y in ulist:
		if ndemand+nodes[x][3]<=nsupply:
			ndemand+=nodes[x][3]
			node_groups[x]=k
	#print "add", addlist[idx][1],[biobjective,objective,objective_overload],
	update_district_info()
	#print "add",addlist[idx][1],biobjective,ulist
	if spatial_contiguity>=1: repair_fragmented_solution()
	return 1

def r_r_location_drop_greedy(): #tested?
	global centersID
	global node_groups
	if adaptive_number_of_facilities==0: return 0
	if objective_supply<total_pop: 
		#print "drop objective_supply<total_pop: ", objective_supply 
		return 0
	dlist=[]
	clist=[x for x in range(num_districts) if centersID[x]>=0 and objective_supply-facilityCapacity[x]>=total_pop]
	if clist==[]: return 0
	for k in clist:
		ids=centersID[:]
		ids[k]=-1
		if locations_exist(ids)==1: continue
		if ids in location_tabu_list: continue
		ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x]==k]
		ulist.sort(key=lambda x:-x[1])
		savings=district_info[k][2]
		if fixed_cost_obj==1: savings+=facilityCost[k]
		caplist=[facilityCapacity[x]-district_info[x][1] for x in range(num_districts)]
		caplist[k]=0
		for x,y in ulist:
			assigned=0
			for r in NearFacilityList[x]:
				if centersID[r]<0: continue
				if r==k: continue
				if y<=caplist[r]:
					savings-=nodedik[x][r]
					caplist[r]-=y
					assigned=1
					break
			if assigned==0:
				for r in NearFacilityList[x]:
					if centersID[r]<0: continue
					if r==k: continue
					#if caplist[r]<=0: continue
					savings-=nodedik[x][r]
					caplist[r]-=y
					break
		surplus=sum(x for x in caplist if x <0) #negitive
		if surplus<-district_info[k][1]*0.05: continue
		savings+=surplus*avg_dis_min*5
		if savings<-biobjective*0.02: continue
		dlist.append([k,savings])
	if len(dlist)==0: return 0 #fail
	dlist.sort(key=lambda x:-x[1])
	if dlist[0][1]>0:
		while dlist[-1][1]<0: dlist.pop()
	r=random.random()
	idx=int(r*r*0.999*min(5,len(dlist)))
	k=dlist[idx][0]
	centersID[k]=-1
	
	ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x]==k]
	ulist.sort(key=lambda x:-x[1])
	caplist=[district_info[x][3]-district_info[x][1] for x in range(num_districts)]
	caplist[k]=0
	for x,y in ulist:
		assigned=0
		for r in NearFacilityList[x]:
			if centersID[r]<0: continue
			if y<=caplist[r]:
				caplist[r]-=y
				node_groups[x]=r
				assigned=1
				break
		if assigned==0:
			for r in NearFacilityList[x]:
				if centersID[r]<0: continue
				caplist[r]-=y
				node_groups[x]=r
				break
	#ulist=[x for x in range(num_units) if node_groups[x]==k]
	#for x in ulist:
	#    for k in NearFacilityList[x]:
	#        if centersID[k]>=0:
	#            node_groups[x]=k
	#            break
	update_district_info()
	#print "drop",dlist[idx][1],[biobjective,objective,objective_overload]
	if spatial_contiguity>=1: repair_fragmented_solution()
	return 1

def select_region(seed):
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	n=nf
	if nf<=7: 
		n=nf
	if nf>=8 and nf<=11: 
		n=random.randint(nf/2+1,8)
	if nf>=12: 
		n=random.randint(7,10)
	#if location_problem==3: n=min(128,num_districts/10)
	u=seed
	if u<0: 
		u=random.randint(0,num_units-1)
	if objective_overload>0 and random.random()>0.2: #SAP
		rlist=[k for k in range(num_districts) if district_info[k][4]>0]
		random.shuffle(rlist)
		r=rlist[0]
		u=nearCustomer[r]
	dlist=[]
	for k in NearFacilityList[u]:
		if centersID[k]<0: continue
		dlist.append(k)
		if len(dlist)==n: break
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]    
	cflist=[]
	for k in range(num_districts):
		if centersID[k]>=0: continue
		if k in exclusion: continue
		'''if k in inclusion: 
			cflist.append([k,0.0])
			continue'''
		d=sum(nodedik[x][k] for x in ulist)
		cflist.append([k,d])
	cflist.sort(key=lambda x: x[1])
	clist=[x[0] for x in cflist]
	clist=clist[:n*num_districts/nf-n]
	clist+=[NearFacilityList[x][0] for x in ulist ]
	clist=list(set(clist))
	clist=[x for x in clist if centersID[x]<0]
	random.shuffle(clist)
	return dlist, clist
def select_corridor_region():
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	n=100*nf/num_units  #areas with 100 units
	if nf<=12: 
		return [x for x in range(num_districts) if centersID[x]>=0],[x for x in range(num_districts) if centersID[x]<0]
	if nf>=12 and nf<=16: 
		n=random.randint(7,10)
	if nf>=17: 
		n=random.randint(8,11)
	#if n*num_units/nf<80: 
	#    n=min(10,80*nf/num_units)
	k_dis=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
		if k in exclusion: continue
		'''if k in inclusion: 
			cflist.append([k,0.0])
			continue'''
		if k not in node_groups:
			k_dis.append([k,MAXNUMBER])
			continue
		dis=max(nodedij[x][k]+district_info[k][4]*penalty_on_demand for x in range(num_units) if node_groups[x]==k)
		k_dis.append([k,dis])
	k_dis.sort(key=lambda x:-x[1])
	r=random.random()
	idx=int(r*r*len(k_dis)/2)
	k=k_dis[idx][0]
	dlist=[k]
	while len(dlist)<n:
		u=nearCustomer[dlist[-1]]
		for k in NearFacilityList[u]:
			if centersID[k]<0: continue
			if k in dlist: continue
			dlist.append(k)
			break
	   
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	clist=[NearFacilityList[x][0] for x in ulist]
	clist+=[NearFacilityList[x][1] for x in ulist ]
	clist=list(set(clist))
	#clist=[x for x in clist if centersID[x]<0 and x not in exclusion]
	random.shuffle(clist)
	return dlist,clist

def select_region_adaptive(seed):
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	units=num_units/nf
	n=-1
	if units >= 50:
		if nf<=10: n=random.randint(nf/2+1,nf)
		if nf>=11 and nf<=20: n=random.randint(8,11)
		if nf>=21: n=random.randint(10,13)
	if units>=25 and units<=49:
		if nf<=10: n=random.randint(nf/2+1,nf)
		if nf>=11 and nf<=20: n=random.randint(9,12)
		if nf>=21: n=random.randint(11,14)
	if units <= 20:
		if nf<=10: n=random.randint(nf/2+1,nf)
		if nf>=11 and nf<=20: n=random.randint(10,13)
		if nf>=21: n=random.randint(12,15)
	n+= len(facility_inclusion_list)*n/nf
	if n>nf: n=nf
	u=seed
	if u<0 or u>=num_units: u=random.randint(0,num_units-1)
	if objective_overload>0 and random.random()>0.2: #SAP
		rlist=[k for k in range(num_districts) if district_info[k][4]>0]
		random.shuffle(rlist)
		r=rlist[0]
		u=nearCustomer[r]
	dlist=[]
	for k in NearFacilityList[u]:
		if centersID[k]<0: continue
		if k in exclusion: continue
		dlist.append(k)
		if len(dlist)==n: break
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]    
	cflist=[]
	for k in range(num_districts):
		if centersID[k]>=0: continue
		d=sum(nodedik[x][k] for x in ulist)
		cflist.append([k,d])
	cflist.sort(key=lambda x: x[1])
	clist=[x[0] for x in cflist]
	clist=clist[:n*num_districts/nf-n]
	clist+=[NearFacilityList[x][0] for x in ulist ]
	clist=list(set(clist))
	clist=[x for x in clist if centersID[x]<0]
	random.shuffle(clist)
	return dlist, clist
def select_region_verylarge(seed):
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	units=num_units/nf
	n=nf/2+1
	u=seed
	if u<0 or u>=num_units: u=random.randint(0,num_units-1)
	r=node_groups[u]
	clist=[]
	for k in NearFacilityList[u]:
		if centersID[k]<0: continue
		if k in exclusion: continue
		clist.append(k)
		if len(clist)==n: break
	return clist

def select_region_lscp():
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	if nf<=10: n=random.randint(nf/2+1,nf)
	if nf>=11 and nf<=20:
		 n=random.randint(8,max(10,nf/2))
	if nf>=21 and nf<=30: 
		n=random.randint(10,15)
	if nf>=31: 
		n=random.randint(nf/3,nf/2)
	u=random.randint(0,num_units-1)
	r=node_groups[u]
	clist=[r]
	for k in NearFacilityList[u]:
		if centersID[k]<0: continue
		if k==r: continue
		clist.append(k)
		if len(clist)==n: break
	return clist

def locations_exist(ids):
	exist=0
	for x in all_solutions:
		if ids==x[1]:
			exist=1
			break
	return exist

def r_r_location_swap_greedy():#tested
	##bug: a far-and-cheap location will be selected
	global centersID
	global node_groups
	dnlist=[]
	klist=[x for x in range(num_districts) if centersID[x]>=0]
	clist=[x for x in range(num_districts) if centersID[x]<0 and x in potential_facilities]
	if clist==[]: return 0  
	supply=sum(facilityCapacity[x] for x in klist)
	random.shuffle(klist)
	random.shuffle(clist)
	location_tabu=[]
	for k in klist:
		#ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x]==k]
		#ulist.sort(key=lambda x: -x[1])
		#ulist=[x[0] for x in ulist]
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		findswap=0
		for j in clist:
			if objective_supply-facilityCapacity[k] +facilityCapacity[j]<min(objective_supply,total_pop): continue
			ids=centersID[:]
			ids[k]=-1
			ids[j]=facilityCandidate[j]
			if ids in location_tabu_list: continue
			#if locations_exist(ids)==1: continue
			savings=district_info[k][2]
			savings-=sum(nodedik[x][j] for x in ulist)
			if facilityCapacity[j] <facilityCapacity[k]:
				savings-=(facilityCapacity[k]-facilityCapacity[j])*avg_dis_min*2
			if fixed_cost_obj==1:
				savings+=facilityCost[k] - facilityCost[j]
			if savings>biobjective*0.0005 and facilityCapacity[j] >=facilityCapacity[k]:
				dnlist=[[k,j,savings]]
				findswap=1
				break
			if savings< -biobjective*0.02: continue
			dnlist.append([k,j,savings])
		if len(dnlist)>20: break
		if findswap==1: break
	if len(dnlist)==0: return 0
	dnlist.sort(key=lambda x: -x[2]) 
	#if dnlist[0][2]>0:
	#    while dnlist[-1][2]<0: dnlist.pop()    

	r=random.random()
	idx=int(r*r*0.999*min(5,len(dnlist)))
	#print [len(dnlist),idx,dnlist[idx][2] ]
	dk=dnlist[idx][0]
	nk=dnlist[idx][1]
	#print "swap",dnlist[idx][0],dnlist[idx][1],dnlist[idx][2]
	#print district_info[dk]
	#---------------assignment 
	centersID[dk]=-1
	centersID[nk]=facilityCandidate[nk]
	district_info[nk][1]=0
	district_info[nk][3]=facilityCapacity[nk]
	ulist=[x for x in range(num_units) if node_groups[x]==dk]
	for x in ulist: node_groups[x]=nk
	
#    ulist=[[x,nodedij[x][nk]] for x in range(num_units) if node_groups[x]==dk]
#    ulist.sort(key=lambda x:x[1])
#    for x,y in ulist:
#        node_groups[x]=-1
#        for r in NearFacilityList[x]:
#            if centersID[r]<0: continue
#            if y<=district_info[r][3]-district_info[r][3]:
#                node_groups[x]=r
#                district_info[r][3]
#                break
#    ulist=[x for x in range(num_units) if node_groups[x]==-1]
#    for x in ulist:
#        for r in NearFacilityList[x]:
#            if centersID[r]<0: continue
#            node_groups[x]=r
#            district_info[r][3]
#            break
	#print dnlist
	#print "swap",dnlist[idx][2],[biobjective,objective,objective_overload],
	#reassign([dk],[nk])
	update_district_info()
	#print district_info[nk]

	#print "swap", dnlist[idx][2],[biobjective,objective,objective_overload]
	#print sum(nodedik[x][dk] for x in ulist),sum(nodedik[x][nk] for x in ulist)
	if spatial_contiguity>=1: repair_fragmented_solution()
	return 1


def r_r_reselect_location_pmp():
	global centersID
	global node_groups
	dlist=select_region(-1)
	#ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	#old_dis=sum(district_info[x][2] for x in dlist)
	try_count=0
	maxcount=200
	best_nlist=[]
	best_dis=MAXNUMBER
	while 1:
		try_count+=1
		if try_count>=maxcount: break
		nlist=[]
		for x in dlist:
			r=random.random()
			idx=max(num_units/5.0/max_num_facility,len(node_neighbors[x]))
			idx=int(idx*pow(r,1.7)*0.9999)
			#rlist=NearFacilityList[x]
			#random.shuffle(rlist)
			nlist.append(NearFacilityList[x][idx])
		if nlist==dlist: continue
		if len(set(nlist+dlist))-len(dlist) <=0: continue
		newdis=0.0
		nlist+=[x for x in range(num_districts) if centersID[x]>=0 and x not in dlist]
		for x in range(num_units):
			for k in NearFacilityList[x]:
				if k in nlist:
					newdis+=nodedik[x][k]
					break
		newdis-=objective
		if newdis<best_dis:
		   best_dis=newdis
		   best_nlist=nlist[:]
		#if newdis<delta: break
	nlist=best_nlist
	#print [int(best_dis)], [x for x in nlist if x not in centersID],
	if best_nlist==[]: return 0
	for x in dlist: centersID[x]=-1
	for x in nlist: centersID[x]=facilityCandidate[x]
	clist=[x for x in range(num_districts) if centersID[x]>=0]
	for x in range(num_units):
		for k in NearFacilityList[x]:
			if k in clist:
				node_groups[x]=k
				break
	obj=objective
	update_district_info()
	#print int(objective-obj),
	if spatial_contiguity>=1: repair_fragmented_solution()
	return 1 

def reassign_geo(dlist,nlist):
	global node_groups
	if spatial_contiguity>=1:
		ulist=[x for x in range(num_units) if node_groups[x] in dlist]
		for x in ulist: node_groups[x]=-1
		for x in ulist:
			for k in NearFacilityList[x]:
				if centersID[k]<0: continue
				node_groups[x]=k
				break
		update_district_info()
		return

	ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x] in dlist]
	ulist.sort(key=lambda x:-x[1])
	ulist=[x[0] for x in ulist]
	for x in ulist: node_groups[x]=-1
	for x in nlist: 
		district_info[x][1]=0
		district_info[x][3]=facilityCapacity[x]

	for x in ulist:
		for k in NearFacilityList[x]:
			#if k not in nlist: continue
			if centersID[k]<0: continue
			if district_info[k][1]+nodes[x][3]<=district_info[k][3]:
				node_groups[x]=k
				district_info[k][1]+=nodes[x][3]
				break
	ulist=[x for x in ulist if node_groups[x]<0]
	for x in ulist:
		for k in NearFacilityList[x]:
			if centersID[k]<0: continue  
			#if k not in nlist: continue
			node_groups[x]=k
			break
	update_district_info()

def reassign(dlist,nlist):
	global node_groups
	if spatial_contiguity>=1:
		return reassign_geo(dlist,nlist)
	ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x] in dlist and node_groups[x] not in nlist]
	ulist.sort(key=lambda x:-x[1])
	ulist=[x[0] for x in ulist]
	for x in ulist: node_groups[x]=-1
	for x in nlist: 
		if x in dlist and x in nlist: continue 
		if x in dlist and x not in nlist: 
			district_info[x][1]=0
			district_info[x][3]=0
		if x not in dlist and x in nlist: 
			district_info[x][1]=0
			district_info[x][3]=facilityCapacity[x]

	for x in ulist:
		for k in NearFacilityList[x]:
			if k not in nlist: continue
			if centersID[k]<0: continue
			if district_info[k][1]+nodes[x][3]<=district_info[k][3]:
				node_groups[x]=k
				district_info[k][1]+=nodes[x][3]
				break
	ulist=[x for x in ulist if node_groups[x]<0]
	for x in ulist:
		for k in NearFacilityList[x]:
			if centersID[k]<0: continue  
			node_groups[x]=k
			break
	update_district_info()

#r&r method
#assign the removed units to solution
def repair_partial_solution():
	global node_groups
	#if spatial_contiguity!=1:
	#    repair_partial_solution_nonconnectivity()
	#    return
	ulist=[x for x in range(num_units) if node_groups[x]==-1] # units not assigned
	for x in ulist:
		d=MAXNUMBER
		k=-1
		for y in range(num_districts):
			if centersID[y]<0: continue
			if nodedik[x][y]<d:
				d=nodedik[x][y]
				k=y
		node_groups[x]=k
	update_district_info()
  
#r&r method
#ruin a region and recreate it
def r_r_perb_district():
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	num=int(nf*ruin_percentage/100)
	if num<1: num=1
	for i in range(num): r_r_perb_a_district()
	update_district_info()
	if spatial_contiguity>=1: repair_fragmented_solution()  
def r_r_perb_a_district():
	global node_groups
	k=random.randint(0, num_districts-1)
	while centersID[k]<0:
		k=random.randint(0, num_districts-1)
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	for x in ulist:
		for k in NearFacilityList[x]:
			if centersID[k]>=0:
				node_groups[x]=k
				break
	update_district_info()

def r_r_perb_mutation():
	global node_groups
	rate=ruin_percentage
	ulist=find_edge_units()
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	num=int(num_units*rate)
	#num=max(2,nf/2)
	#if location_problem==3: num=max(5,nf/4)

	if num<1: num=1
	for x in ulist:
		#if x in centersID: continue        
		if node_groups[x]==x and location_problem==3: continue
		for y in node_neighbors[x]:
			if node_groups[x]!=node_groups[y]:
				node_groups[x]=node_groups[y]
				num-=1
				break
		if num<=0:
			break
	update_district_info()
	#if spatial_contiguity>=1: repair_fragmented_solution()

#update the best and the global best solution
#if the current solution is better than the best
def update_best_solution():
	global best_solution
	global best_centersID
	global best_biobjective
	global best_objective
	global best_objective_fcost
	global best_overload
	global best_objective_overload
	global best_centersID_global
	global best_solution_global
	global best_biobjective_global
	global best_objective_global
	global best_objective_fcost_global
	global best_overload_global    
	global improved_loop
	global improved
	global avg_dis_min
	improve =0
	if location_problem==1 and adaptive_number_of_facilities==0:
		nf=sum(1 for x in centersID if x>=0)
		if nf!=max_num_facility: return 0
	#if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
	#    ##noprint "check_solution_continuality_feasibility!!!"
	#    return improve
	biobj=biobjective
	biobj_best=best_biobjective
	if biobj<=biobj_best:
		best_biobjective=biobj
		best_objective = objective
		best_objective_fcost=objective_fcost
		best_objective_overload = objective_overload
		best_solution = node_groups[:]
		best_centersID=centersID[:]
		improved_loop=mainloop
		improve =1
		improved+=1
	if biobj<best_biobjective_global:
		best_biobjective_global=biobj
		best_centersID_global=centersID[:]
		best_overload_global = objective_overload
		best_solution_global =node_groups[:]
		best_objective_global = objective
		best_objective_fcost_global=objective_fcost
		avg_dis_min=biobj/total_pop
	return improve

#return the neighor regions of unit nid
def neighbor_regions(nid):
	rid=node_groups[nid]
	if spatial_contiguity>=1:
		rlist2=[node_groups[x] for x in node_neighbors[nid] if node_groups[x]!=rid]
		rlist=list(set(rlist2))
		if len(rlist2)>1: random.shuffle(rlist2)
		return rlist
	if spatial_contiguity>=0 and random.random()>0.5: #testing ??? 
		knn=4
		#if knn< num_units/100: knn=num_units/100
		rlist=[]
		for k in NearFacilityList[nid]:
			if k==rid: continue
			if centersID[k]<0: continue
			rlist.append(k)
			if len(rlist)>=knn: break 
		return rlist
	rlist2=[node_groups[x] for x in node_neighbors[nid] if node_groups[x]!=rid]
	rlist=list(set(rlist2))
	if len(rlist2)>1: random.shuffle(rlist2)
	return rlist

#evaluate the possible moves
#return 0 or 1 according to the acceptance rule
#acceptance rule: sa, rrt, oba or others
def isbetter(obj_old,obj_new,bal_old,bal_new):
	#fixed cost is not considered
	penalty=penalty_on_demand
	biobj_new=objective-obj_old+obj_new+bal_new*penalty
	biobj_old=objective+objective_overload*penalty
	if biobj_new<biobj_old-0.000001: #better
		return 1
	if bal_new>bal_old: return 0 #more overload, or not reduce the overload
	if acceptanceRule=="rrt":
		if objective+obj_new-obj_old-best_objective<best_objective*1.0/num_units:
			if random.random()>0.5: return 0
			else: 
				#print ".",
				return 1
	if acceptanceRule=="sa":
		#minobj=min(last_loop_obj,biobjective)
		#a=-(biobj_new-minobj)/minobj*num_units/SA_temperature
		a=-(objective+obj_new-obj_old-best_objective)/best_objective*num_units/SA_temperature
		if a>=0: return 1
		p=math.exp(a)
		if random.random()< p:  return 1
	return 0

def one_unit_move(): #FA
	global node_groups
	global time_op
	global count_op
	if location_problem==3:
		return one_unit_move_pmp_geo()
	#if location_problem==0:
	#   return one_unit_move_SAP()
	if spatial_contiguity>=1 or location_problem==2:
		return one_unit_move_geo()
	t=time.time()
	ulist=find_edge_units()
	difflist=[]
	for x in ulist:
		rlist=[r for r in NearFacilityList[x] if centersID[r]>=0]
		k=node_groups[x]
		difflist.append([x,nodedik[x][rlist[0]]-nodedik[x][k]])
	difflist.sort(key=lambda x:x[1])
	ulist=[x[0] for x in difflist]
	find_best_solution=0
	update_cflpr_district_info()
	for nid in ulist:
		rid=node_groups[nid]
		demand=nodes[nid][3]
		klist=neighbor_regions(nid)
		if len(klist)>1:
			klist2=[x for x in NearFacilityList[nid] if x in klist]
			klist=klist2
		for k in klist:
			#if k==rid: print "k==rid", nid,rid,neighbor_regions(nid)
			if demand+district_info[k][1]>facilityCapacity[k]: continue
			savings=nodedik[nid][rid]-nodedik[nid][k]
			overload_old=district_info[rid][4]+district_info[k][4]
			overload_new= max(0,district_info[rid][1]-nodes[nid][3]-facilityCapacity[rid]) +max(0,district_info[k][1]+nodes[nid][3]-facilityCapacity[k])
			savings*=travel_distance_weight
			savings+= (overload_old-overload_new)*penalty_on_demand
			if envy_service_objective==1:
				if nodedij[nid][rid]>envy_service_distance:
					savings+= nodes[nid][3]*envy_objective_weight*(nodedij[nid][rid]-envy_service_distance)*(nodedij[nid][rid]-envy_service_distance)
				if nodedij[nid][k]>envy_service_distance:
					savings-= nodes[nid][3]*envy_objective_weight*(nodedij[nid][k]-envy_service_distance)*(nodedij[nid][k]-envy_service_distance)
			if envy_service_objective==4:
				if nodedij[nid][rid]>envy_service_distance:
					savings+= nodes[nid][3]*envy_objective_weight*(nodedij[nid][rid]-envy_service_distance)
				if nodedij[nid][k]>envy_service_distance:
					savings-= nodes[nid][3]*envy_objective_weight*(nodedij[nid][k]-envy_service_distance)
			if savings<=0.0001: continue
			node_groups[nid]=k
			count_op[0]+=1
			#print "OUM",savings,biobjective,objective,objective_overload,
			update_cflpr_district_info()
			#print "->",biobjective,objective,objective_overload
			find_best_solution += 1#update_best_solution()
			break
	if spatial_contiguity>=1: repair_fragmented_solution()
	time_op[0]+=time.time()-t
	return find_best_solution

#move one edge unit to its neighbor region
def one_unit_move_geo():
	#global district_info
	if location_problem==3: #pdp or homoDP
		return one_unit_move_pmp_geo()
	global node_groups
	global time_op
	global count_op
	popa=0.0
	if location_problem==2:
		popa=total_pop*1.0/max_num_facility #location_problem==2
	dev=pop_deviation*popa
	update_cflpr_district_info()

	t=time.time()
	improve = 0
	ulist=find_edge_units()
	find_best_solution=0
	for n1 in ulist:
		k1 = node_groups[n1]
		for k2 in neighbor_regions(n1):
			obj_new = nodedik[n1][k2]
			obj_old = nodedik[n1][k1]
			old_bal=district_info[k1][4]+district_info[k2][4]
			new_pop1=district_info[k1][1]-nodes[n1][3]
			new_pop2=district_info[k2][1]+nodes[n1][3]
			new_bal=max(0,new_pop1-facilityCapacity[k1]) + max(0,new_pop2-facilityCapacity[k2])
			if location_problem==2: 
				new_bal=0.0
				if new_pop1 >popa+dev: new_bal+=new_pop1-popa-dev
				if new_pop2 >popa+dev: new_bal+=new_pop2-popa-dev
				if new_pop1 <popa-dev: new_bal+=popa-dev-new_pop1
				if new_pop2 <popa-dev: new_bal+=popa-dev-new_pop2
			#if isbetter(obj_old,obj_new,old_bal,new_bal)==0:
			if isbetter(obj_old,obj_new,objective_overload,objective_overload-old_bal+new_bal)==0:
				continue
			sol=node_groups[:]
			sol[n1] = k2
			if spatial_contiguity>=1 and check_continuality_feasibility(sol,k1)==0:
				break
			count_op[0]+=1
			node_groups[n1] = k2
			obj=biobjective
			objb=best_objective
			update_cflpr_district_info()
			find_best_solution += 1# update_best_solution()
			break
	if spatial_contiguity==1: repair_fragmented_solution()
	time_op[0]+=time.time()-t
	return find_best_solution
def one_unit_move_pmp_geo():
	#global district_info
	global node_groups
	global time_op
	global count_op
	t=time.time()
	improve = 0
	ulist=find_edge_units()
	find_best_solution=0
	for n1 in ulist:
		k1 = node_groups[n1]
		for k2 in neighbor_regions(n1):
			if nodedik[n1][k2] >= nodedik[n1][k1]: continue
			sol=node_groups[:]
			sol[n1] = k2
			#if spatial_contiguity>=1 and check_continuality_feasibility(sol,k1)<=0: break
			count_op[0]+=1
			node_groups[n1] = k2
			update_district_info()
			#find_best_solution += update_best_solution()
			#break
	time_op[0]+=time.time()-t
	if spatial_contiguity>=0:
		repair_fragmented_solution()
	return find_best_solution
def pmp_VND_search():
	global node_groups
	global time_op
	global count_op
	improved = 0
	t=time.time()
	if spatial_contiguity==0: return 0
	while 1:
		improve = 0
		#if spatial_contiguity==0:
		ulist=find_edge_units()
		for u in ulist:
			k=node_groups[u]
			for u2 in node_neighbors[u]:
				if node_groups[u2]==k: continue
				k2=node_groups[u2]
				if nodedik[u][k2]>=nodedik[u][k]: continue
				#if spatial_contiguity>=1: 
				#    ulist2=[x for x in range(num_units) if node_groups[x]==k and x!=u]
				#    if ulist2==[]: continue
				#    if check_ulist_continuality(ulist2)==0: continue
				node_groups[u] = k2
				improve+=1
				improved+=1
		if improve == 0: break
	time_op[0]+=time.time()-t
	#print "improved",improved,
	update_district_info()
	return improved
def two_unit_move():
	#if location_problem==0:
	#   return two_unit_move_SAP()
	if spatial_contiguity==1 or location_problem==2:
		return two_unit_move_geo()
	global node_groups
	global time_op
	global count_op
	t=time.time()
	find_best_solution=0
	improve = 0
	ulist=find_edge_units()
	if ulist==[]:
		ulist=range(num_units)
	difflist=[]
	update_cflpr_district_info()

	for x in ulist:
		rlist=[r for r in NearFacilityList[x] if centersID[r]>=0]
		k=node_groups[x]
		difflist.append([x,nodedij[x][rlist[0]]-nodedij[x][k]])
	if len(difflist)==0:
		print "debug: two_unit_move(): len(difflist)==0"
	difflist.sort(key=lambda x:x[1])
	ulist=[x[0] for x in difflist]
	nu=len(ulist)/2
	fulist=ulist[:nu]
	movelist =[]
	for n1 in ulist:
		k1 = node_groups[n1]
		rlist1=neighbor_regions(n1)
		success_move=0
		ulist2=[x for x in ulist if node_groups[x] in rlist1]
		random.shuffle(ulist2)
		for n2 in ulist2:
			#if n1 == n2: continue
			k2=node_groups[n2]
			#if k2 not in rlist1: continue
			#if district_info[k2][1]+nodes[n1][3]-nodes[n2][3]-facilityCapacity[k2] >district_info[k2][4]: continue
			for k3 in neighbor_regions(n2):
				#if k3!=k1 and district_info[k3][1]+nodes[n2][3]>facilityCapacity[k3]: continue
				#if k3==k1 and district_info[k3][1]-nodes[n1][3]+nodes[n2][3]-facilityCapacity[k3]>district_info[k3][4]: continue
				savings=nodedik[n1][k1]+nodedik[n2][k2]
				savings-=nodedik[n1][k2]+nodedik[n2][k3]
				savings*=travel_distance_weight

				if envy_service_objective==1:
					if nodedij[n1][k1]>envy_service_distance:
						savings+= nodes[n1][3]*envy_objective_weight*(nodedij[n1][k1]-envy_service_distance)*(nodedij[n1][k1]-envy_service_distance)
					if nodedij[n2][k2]>envy_service_distance:
						savings+= nodes[n2][3]*envy_objective_weight*(nodedij[n2][k2]-envy_service_distance)*(nodedij[n2][k2]-envy_service_distance)
					if nodedij[n1][k2]>envy_service_distance:
						savings-= nodes[n1][3]*envy_objective_weight*(nodedij[n1][k2]-envy_service_distance)*(nodedij[n1][k2]-envy_service_distance)
					if nodedij[n2][k3]>envy_service_distance:
						savings-= nodes[n2][3]*envy_objective_weight*(nodedij[n2][k3]-envy_service_distance)*(nodedij[n2][k3]-envy_service_distance)
				if envy_service_objective==4:
					if nodedij[n1][k1]>envy_service_distance:
						savings+= nodes[n1][3]*envy_objective_weight*(nodedij[n1][k1]-envy_service_distance)
					if nodedij[n2][k2]>envy_service_distance:
						savings+= nodes[n2][3]*envy_objective_weight*(nodedij[n2][k2]-envy_service_distance)
					if nodedij[n1][k2]>envy_service_distance:
						savings-= nodes[n1][3]*envy_objective_weight*(nodedij[n1][k2]-envy_service_distance)
					if nodedij[n2][k3]>envy_service_distance:
						savings-= nodes[n2][3]*envy_objective_weight*(nodedij[n2][k3]-envy_service_distance)

				savings2=0
				if k3!=k1:
					slist=[district_info[k1][1]-nodes[n1][3],district_info[k2][1]+nodes[n1][3]-nodes[n2][3],district_info[k3][1]+nodes[n2][3]]
					savings2=district_info[k1][4]+district_info[k2][4]+district_info[k3][4]
					savings2-=max(0,slist[0]-facilityCapacity[k1])+max(0,slist[1]-facilityCapacity[k2])+max(0,slist[2]-facilityCapacity[k3])
				if k3==k1:
					slist=[district_info[k1][1]-nodes[n1][3]+nodes[n2][3],district_info[k2][1]+nodes[n1][3]-nodes[n2][3]]
					savings2=district_info[k1][4]+district_info[k2][4]
					savings2-=max(0,slist[0]-facilityCapacity[k1])+max(0,slist[1]-facilityCapacity[k2])
				#if district_info[k1][4]==0 and savings<0: continue
				savings+= savings2*penalty_on_demand
				#if savings2<0: continue
				#if savings2==0 and savings<0: continue
				if savings<=0: continue
				count_op[1]+=1
				sp=objective_supply
				node_groups[n1] = k2
				node_groups[n2] = k3
				obj=biobjective
				#print "TUM",biobjective,objective,objective_overload,
				sp=objective_supply
				update_cflpr_district_info()
				#print "->",biobjective,objective,objective_overload,":",savings,savings2,biobjective-obj
				find_best_solution += 1#update_best_solution()
				success_move=1
				break
			if success_move==1: break            
	if spatial_contiguity==1: repair_fragmented_solution()
	time_op[1]+=time.time()-t
	return find_best_solution

#for a region
#move out one edge unit to its neighbor region, and
#move in one edge unit from its neighbor region
def two_unit_move_geo():
	#global district_info
	global node_groups
	global time_op
	global count_op
	popa=0.0
	if location_problem==2:
		popa=total_pop*1.0/max_num_facility #location_problem=2,PDP
	dev=popa*pop_deviation

	t=time.time()
	find_best_solution=0
	improve = 0
	ulist=find_edge_units()
	movelist=[]
	update_cflpr_district_info()

	difflist=[]
	for x in ulist:
		rlist=[r for r in NearFacilityList[x] if centersID[r]>=0]
		k=node_groups[x]
		difflist.append([x,district_info[k][4]*100000+nodedij[x][rlist[0]]-nodedij[x][k]])
	difflist.sort(key=lambda x:x[1])
	ulist_n1=[x[0] for x in difflist]
	ulist_n1=ulist[:]
	random.shuffle(ulist_n1)
	for n_id1 in ulist_n1:
		r_id1 = node_groups[n_id1]
		rlist1=neighbor_regions(n_id1)
		success_move=0
		for n_id2 in ulist:
			if n_id1 == n_id2: continue
			#if n_id1 in movelist: break
			#if n_id2 in movelist: continue
			if node_groups[n_id2] not in rlist1: continue
			new_r_id1=node_groups[n_id2]
			r_id2 = node_groups[n_id2]
			#sol=node_groups[:]
			#sol[n_id2] = -1
			#if spatial_contiguity==1 and check_continuality_feasibility(sol,r_id2)==0:
			#    movelist.append(n_id2)
			#    continue
			success_move=0
			for new_r_id2 in neighbor_regions(n_id2):
				obj_new = nodedik[n_id1][new_r_id1] + nodedik[n_id2][new_r_id2]
				obj_old = nodedik[n_id1][r_id1]+nodedik[n_id2][r_id2]
				new_district_info = [x[1] for x in district_info]
				new_district_info[r_id1] -= nodes[n_id1][3]
				new_district_info[r_id2] -= nodes[n_id2][3]
				new_district_info[new_r_id1] += nodes[n_id1][3]
				new_district_info[new_r_id2] += nodes[n_id2][3]
				bal=0.0
				bal=sum(new_district_info[x]-facilityCapacity[x] for x in range(num_districts) if new_district_info[x]>facilityCapacity[x])
				if location_problem==2:
					bal=0.0
					for x in new_district_info:
						if x==0: continue
						if x >popa+dev: bal+=x-popa-dev
						if x <popa-dev: bal+=popa-dev-x
				#yfkong
				#if bal>objective_overload: continue
				if isbetter(obj_old,obj_new,objective_overload,bal)==0:
					continue
				sol=node_groups[:]
				sol[n_id1] = new_r_id1
				sol[n_id2] = new_r_id2
				if spatial_contiguity>=1 and check_continuality_feasibility(sol,r_id1)==0:
					#movelist.append(n_id1)
					success_move=1
					break
				if spatial_contiguity>=1 and check_continuality_feasibility(sol,r_id2)==0:
					#movelist.append(n_id2)
					success_move=1
					break
				count_op[1]+=1
				node_groups[n_id1] = new_r_id1
				node_groups[n_id2] = new_r_id2
				#movelist.append(n_id1)
				#movelist.append(n_id2)
				obj=objective
				#print [2,obj_old,obj_new,objective_overload,bal,biobjective],
				update_cflpr_district_info()
				#print biobjective
				#if objective-obj> obj_new-obj_old+0.01:
				#     print "debug oum!!!"
				find_best_solution += 1#update_best_solution()
				success_move=1
				break
			if success_move==1: break
	if spatial_contiguity==1: repair_fragmented_solution()
	time_op[1]+=time.time()-t
	return find_best_solution

# local search
def RRT_local_search():
	#if location_problem==3:
	#    pmp_VND_search()
	#    return
	global improved
	#global node_neighbors
	improved=0
	#operators=[0,1,2,3,4]
	operators=assignment_operators_selected[:]
	#if op_random == 1 and random.random()>0.5:
	#    random.shuffle(operators)
	for op in operators:
		if op == 0:
			one_unit_move()
			#update_region_pool_all()
		if op == 1:
			two_unit_move()
			#update_region_pool_all()
	return

#local search with operator op
def vnd_op_search(op):
	#global node_neighbors
	#for x in node_neighbors:
	#    random.shuffle(x)
	imp=0    
	obj=biobjective    
	if op == 0:
		imp=one_unit_move()
	if op == 1:
		imp=two_unit_move()
	if op == 2:
		imp=0
	if op == 3:
		imp=0
	#print [op,imp,biobjective - obj]        
	return imp

#VND search
def VND_local_search():
	#if location_problem==3:
	#    pmp_VND_search()
	#    return
	global improved
	improved=0
	#operators=[0,1,2,3,4]
	operators=assignment_operators_selected[:]    
	if len(operators)==0: return
	#if op_random == 1:
	#if op_random == 1 and random.random()>0.5:
	#    random.shuffle(operators)
	obj=biobjective
	while 1:
		imp=vnd_op_search(operators[0])
		if biobjective < obj-0.00001:
			obj=biobjective
			continue
		if len(operators)==1:break
		vnd_op_search(operators[1])
		if biobjective < obj-0.00001:
			obj=biobjective
			continue
		if len(operators)==2:break
		vnd_op_search(operators[2])
		if biobjective < obj-0.00001:
			obj=biobjective
			continue
		if len(operators)==3:break
		vnd_op_search(operators[3])
		if biobjective < obj-0.00001:
			obj=biobjective
			continue
		if len(operators)==4:break
		vnd_op_search(operators[4])
		if biobjective < obj-0.00001:
			obj=biobjective
			continue
		break
	return

#VNs search
def vns_op_search(op):
	#global node_neighbors
	global node_groups
	node_groups=best_solution[:]
	update_district_info()
	obj=biobjective
	shake(op*2+2)
	#assign_ruin_recreate()
	#VND_local_search()
	vnd_op_search(op)
	#update_region_pool_all()
	return obj-biobjective

def shake(k):
	global node_groups
	if k<1: return
	ulist=find_edge_units()
	counter=0
	for uid in ulist:#(int(num_units*rate+0.5)):
		rid=node_groups[uid]
		r=neighbor_regions(uid)
		if len(r)<1: continue
		random.shuffle(r)
		node_groups[uid]=r[0]
		counter+=1
		if counter>=k: break
	if spatial_contiguity>1: repair_fragmented_solution()
	else: update_district_info()
	
def VNS_local_search():
	global improved
	improved=0
	operators=assignment_operators_selected
	count=0
	while 1:
		count+=1
		objimprove=vns_op_search(operators[0])
		if objimprove>0.00001:  continue
		if len(operators)==1:break

		count+=1
		objimprove=vns_op_search(operators[1])
		if objimprove>0.00001:  continue
		if len(operators)==2:break

		count+=1
		objimprove=vns_op_search(operators[2])
		if objimprove>0.00001: continue
		break
	return
def read_pmp_climate_instance(f1,f2,num_feat,num_first): #climate data
	global num_units
	global nodes
	global nodes_std
	global node_neighbors
	global nodedij
	global nodedik
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global potential_facilities
	global total_pop
	global weight_features
	f = open(f1)
	line = f.readline()
	line=line[:-1]
	items=line.split("\t")
	num_units=int(items[0])
	num_features=int(items[1])
	num_first_feature=4
	if len(items)>=3:
		num_first_feature=int(items[2])
	data_standardlize=1
	if len(items)>=4:
		data_standardlize=int(items[3])
	if num_feat>=1:
		num_features=num_feat
		num_first_feature=num_first
	print "instance size, features, first columme and std.",num_units,num_features,num_first_feature,data_standardlize

	weight_features=[1 for x in range(num_features)]
	line = f.readline()
	line=line[:-1]
	items=line.split("\t")
	for i in range(num_features):
		weight_features[i]=float(items[num_first_feature+i])
	#print weight_features[:10],"..."
	line = f.readline()
	line=line[:-1]
	idx=0
	for i in range(num_units):
		if i%100==0: print ".",
		line = f.readline()
		line=line[:-1]
		items = line.split('\t')
		node=[int(items[0]),float(items[1]),float(items[2]),float(items[3])]
		#items[:num_first_feature]
		for j in range(len(items)):
			if items[j]=="": items[j]="0"
		if data_standardlize<=1:
			attr=[float( items[x+num_first_feature] ) for x in range(num_features)]
		else:
			attr=[items[x+num_first_feature] for x in range(num_features)]
		nodes.append(node+attr)
	f.close()
	num_districts=num_units
	facilityCandidate=range(num_districts)
	facilityCapacity=[num_units for x in range(num_districts)]
	print
	print "num_units, features",num_units, num_features
	print "weights",weight_features
	#print "nodes", nodes[0]
	#print "nodes", nodes[num_units-1]
	nodes_std=[[0.0 for x in range(num_features)] for y in range(num_units)]
	if data_standardlize==0:
		for k in range(num_features):
			if weight_features[k]<0.0000001: continue
			for i in range(num_units):
				nodes_std[i][k]=nodes[i][k+4]*math.sqrt(weight_features[k])
	if data_standardlize==1:
		print "data standardlizing..."
		area_total=sum(x[3] for x in nodes)
		wgt=[x[3] for x in nodes]
		for k in range(num_features):
			if weight_features[k]<0.0000001: continue
			attr=[x[k+4] for x in nodes]
			avg=sum(attr[x]*wgt[x] for x in range(num_units))/area_total
			var=sum(wgt[x]*(attr[x]-avg)*(attr[x]-avg) for x in range (num_units) )
			if var<0.0000001: continue
			var/=area_total
			dev=pow(var,0.5)
			print avg,dev
			for i in range(num_units):
				nodes_std[i][k]=(nodes[i][k+4]-avg)/dev*math.sqrt(weight_features[k])

	nodedik=[[0.0 for x in range(num_units)] for y in range(num_units)]
	#if spatial_contiguity==1:
	nodedij=[[0.0 for x in range(num_units)] for y in range(num_units)]
	#else: nodedij=nodedik
	#nodedij=nodedik
	#print "nodes_std",nodes_std
	if data_standardlize==1:
		print "outlier data:"
		n=0
		'''for j in range(num_features):
			for i in range(num_units):
				x=nodes_std[i][j]
				if x>3 or x<-3: 
					n+=1
					print [nodes[i][0],j, nodes[i][j+4]],
			print
		print "total outlier values (>3, <-3):",n'''
		print "outlier locations:"
		for i in range(num_units):
			s1=sum(abs(x) for x in nodes_std[i])
			s2=max(abs(x) for x in nodes_std[i])
			if s1>7.5 or s2>3.0 : 
				print nodes[i][0],nodes_std[i],nodes[i]
				n+=1
		print
		print "total outlier values (>3, <-3):",n

	print "calculating the matrix ..."
	for i in range(num_units):
		#nodedik[i][i]=0.0
		for j in range(i,num_units):
			if j<=i: continue
			d=0.0
			if data_standardlize==2:
				for k in range(num_features):
					if weight_features[k]<0.00000001: continue
					ai=nodes[i][k+4]
					aj=nodes[j][k+4]
					if ai!=aj: 
						d+=math.sqrt(weight_features[k])
			if data_standardlize<=1:
				d=sum((nodes_std[i][x]-nodes_std[j][x])*(nodes_std[i][x]-nodes_std[j][x]) for x in range(num_features)) #/num_features
			nodedik[i][j]=nodes[i][3]*d
			nodedik[j][i]=nodes[j][3]*d
			nodedij[i][j]=d
			nodedij[j][i]=d
		if i%10==0: print ".",
		#if i>0 and i%(num_units/100) == 0: print str(i)+"/"+str(num_units)
	print
	#print nodedij
	print "creating node neighbors ..."
	#if spatial_contiguity!=1:
	#nodedij=nodedik
	node_neighbors = [[]for x in range(num_units)]
	# for i in range(num_units):
		# id1= nodes[i][3]
		# id2= nodes[i][4]
		# neighb=[]
		# for j in range(num_units):
			# if j==i: continue
			# if abs(id1-nodes[j][3])<=1 and abs(id2-nodes[j][4])<=1:
				# neighb.append(j)
		# node_neighbors[i]=neighb[:]
		# if i%10==0: print ".",
	f = open(f2)
	line = f.readline()
	line = f.readline()
	links=0
	ids=[x[0] for x in nodes]
	while line:
		items = line.split(',')
		if len(items)<=2:
			items = line.split('\t')
		if int (items[1]) != int (items[2]):
			id1=int (items[1])
			id2=int (items[2])
			idx1=-1
			idx2=-1
			for i in range(num_units):
				if nodes[i][0]==id1:
					idx1=i
				if nodes[i][0]==id2:
					idx2=i
				if idx1>=0 and idx2>=0:
					break
			if idx1>=0 and idx2>=0:
				node_neighbors[idx1].append(idx2)
		line = f.readline()
	f.close()
	#print node_neighbors
	#create_facility_neighbors()
	#find_NearFacilityList(num_districts)
	#find_near_customer()
	potential_facilities=[x for x in range(num_districts)]
	print "data prepaird!!"
	total_pop=num_units
	return

def read_pmp_instance(pfile):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	if len(items)==1:
		items = line.split('\t')
	num_units=int(items[0])
	num_districts=int(items[0])
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	for i in range(num_districts):
		line = f.readline()
		line=line[0:-1]
		items = line.split('\t')
		for j in range(num_units):
			nodedik[j][i]=int(items[j])
			nodedij[j][i]=int(items[j])
	#for i in range(num_districts): print nodedik[i]
	line = f.readline()
	line = f.readline()
	line=line[0:-1]
	items = line.split('\t')
	for i in range(num_units):
		facilityCost[i]=int(items[i])
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0

	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	#print "NearFacilityList:"
	#for i in range(num_districts): print NearFacilityList[i]
	find_near_customer()

	for i in range(num_units):
		node_neighbors.append(NearFacilityList[i][:8])

	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_pmp_or_instance(pfile): #read pmed instances
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global max_num_facility
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line=line.strip()
	#line=line[0:-1]
	items = line.split(' ')
	num_units=int(items[0])
	num_districts=int(items[0])
	num_links=int(items[1])
	max_num_facility =int(items[2])   
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N:P "+str(num_districts)+" "+str(num_units) +" "+ str(max_num_facility)) 
	node_neighbors=[ [] for x in range(num_units)]
	links={}
	for i in range(num_links):
		line = f.readline()
		line = line.strip()
		#line=line[0:-1]
		items = line.split(' ')
		n1=int(items[0])-1
		n2=int(items[1])-1
		#print line,items
		links[str(n1)+"_"+str(n2)]=int(items[2])
		links[str(n2)+"_"+str(n1)]=int(items[2])
		node_neighbors[n1].append(n2)
		node_neighbors[n2].append(n1)
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	#for i in range(num_units):
	#     print i, node_neighbors[i]

	#nodedij
	for i in range(num_units):
		dist=[int(MAXNUMBER) for x in range(num_units)]
		dist[i]=0
		inlist=[i]
		while 1:
			if inlist==[]: break
			u=inlist[0]
			del inlist[0]
			for x in node_neighbors[u]:
				if dist[u]+links[str(u)+"_"+str(x)]<dist[x]:
					dist[x]=dist[u]+links[str(u)+"_"+str(x)]
					if x not in inlist: 
						inlist.append(x)
		nodedij[i]=dist[:]
		nodedik[i]=dist[:]
	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	find_near_customer()
	
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_pmp_pm_instance(pfile): #cost???
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line = f.readline() #I,J
	line = f.readline() #I,J
	line=line.strip()
	#line=line[0:-1]
	items = line.split(' ')
	num_units=int(items[0])
	num_districts=int(items[0])
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [1000 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [1000 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	node_neighbors=[ [] for x in range(num_units)]
	links={}
	line = f.readline() #I,J
	line = f.readline() #I,J
	while 1:
		line = line.strip()
		if len(line)<2: break
		items = line.split(' ')
		n=len(items)
		for i in range(1,n+1):
			if items[n-i]=="": del items[n-i]
		n1=int(items[0])-1
		n2=int(items[1])-1
		#links[str(n1)+"_"+str(n2)]=int(items[2])
		nodedij[n2][n1]=int(items[2])
		nodedik[n2][n1]=int(items[2])
		#node_neighbors[n1].append(n2)
		#node_neighbors[n2].append(n1)
		line = f.readline()
	f.close()
	#print node_neighbors
	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	#for i in range(num_units):
	#     print i, node_neighbors[i]

	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	find_near_customer()
	
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_pmp_rw_instance(pfile):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	num_units=int(items[1])
	num_districts=int(items[2])
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	line = f.readline() #I,J
	for idx in range(num_units*num_districts):
		line = f.readline()
		line=line[0:-1]
		items = line.split(' ')
		i=int(items[1])-1
		j=int(items[2])-1
		c=int(items[3])
		nodedik[i][j]=c
		nodedij[i][j]=c
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0

	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	#print "NearFacilityList:"
	#for i in range(num_districts): print NearFacilityList[i]
	find_near_customer()

	#for i in range(num_units):
	#    node_neighbors.append(NearFacilityList[i][:8])
	create_node_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_bm_instance(f1): #read instances from or-lib(beasily),holmberge,yang...
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(f1)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	idx=0
	for item in items:
		if item=="":
			continue
		if idx==0:
			num_districts=int(item)
			idx+=1
		else:
			num_units=int(item)
			idx+=1
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[0.0 for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	for i in range(num_districts):
		line = f.readline()
		line=line[0:-1]
		items = line.split(' ')
		idx=0
		for item in items:
			if item=="":
				continue
			if idx==0:
				facilityCapacity[i]=float(item)
				idx+=1
			else:
				facilityCost[i]=float(item)
				idx+=1
	idx=0
	line = f.readline()
	while line: # for i in range((num_units+1)/10):
		line=line[0:-1]
		items = line.split(' ')
		for item in items:
			if item=="":
				continue
			if idx<num_units:
				nodes[idx][3]=float(item)
				idx+=1
			else:
				#i=(idx-num_units)/num_districts
				#k=(idx-num_units)%num_districts
				i=(idx-num_units)%num_units
				k=(idx-num_units)/num_units
				nodedik[i][k]=float(item)
				nodedij[i][k]=float(item)/nodes[i][3]
				idx+=1
		line = f.readline()    
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	#print NearFacilityList
	find_near_customer()
	create_node_neighbors()
	#find_nearFacilityFacility()
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_bm_instance2(f1):#read tbed instances
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(f1)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	if line.find("\t"): items = line.split('\t')
	idx=0
	for item in items:
		if item=="":
			continue
		if idx==0:
			num_units=int(item)
			idx+=1
		else:
			num_districts=int(item)
			idx+=1
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[0.0 for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))

	idx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			nodes[idx][3]=float(item)
			idx+=1
		if idx==num_units: break

	fidx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			facilityCapacity[fidx]=float(item)
			fidx+=1
		if fidx==num_districts: break
	fidx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			facilityCost[fidx]=float(item)
			fidx+=1
		if fidx==num_districts: break
	idx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			k=idx/num_units
			i=idx%num_units
			idx+=1
			nodedik[i][k]=float(item)*nodes[i][3]
			nodedij[i][k]=float(item)
		if idx==num_units*num_districts: break
	f.close()
	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	find_near_customer()
	#find_nearFacilityFacility()
	create_node_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def create_facility_neighbors():
	return 
	global facility_neighbors
	mindij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_districts)]
	for i in range(num_districts):
		for j in range(num_districts):
			if j<=i: continue
			dlist=[nodedij[x][i]-nodedij[x][j] for x in range(num_units)]
			d=sum(x*x for x in dlist)
			mindij[i][j]=d
			mindij[j][i]=d
	facility_neighbors = [[]for x in range(num_districts)]
	for i in range(num_districts):
		dlist=[[x, mindij[i][x]] for x in range(num_districts) ]
		dlist.sort(key=lambda x:x[1])
		nghrs=[x[0] for x in dlist]
		facility_neighbors[i]=nghrs[:]

def create_node_neighbors():
	global node_neighbors
	#rlist=[x for x in range(num_districts)]
	mindij=[[MAXNUMBER for x in range(num_units)] for y in range(num_units)]
	for i in range(num_units):
		for j in range(num_units):
			if j<=i: continue
			dlist=[nodedij[i][x]-nodedij[j][x] for x in range(num_districts)]
			d=sum(x*x for x in dlist)
			mindij[i][j]=d
			mindij[j][i]=d
	node_neighbors = [[]for x in range(num_units)]
	for i in range(num_units):
		dlist=[[x, mindij[i][x]] for x in range(num_units) ]
		dlist.sort(key=lambda x:x[1])
		nn=8
		if nn>num_units: nn=num_units
		nghrs=[dlist[x][0] for x in range(nn)]
		random.shuffle(nghrs) #debug
		node_neighbors[i]=nghrs[:]

#read instance file, f1:unit info, f2: connectivity info
def readfile(f1,f2):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global facility_inclusion_list
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	#nodes.append(node)
	print "reading nodes ...",
	f = open(f1)
	line = f.readline()  #OID    pop    PointX    PointY    fcadidature    fcost    fcapacity
	line = f.readline()
	nodeidx=0
	while line:
		items = line.split()
		'''line=line[0:-1]
		#print line
		items = line.split(',')
		if len(items)<=2:
			items = line.split()'''
		unit=[nodeidx, float(items[2]), float(items[3]), int(items[1]),int(items[0]),int(items[6]),int(items[4]),float(items[5])]
		nodes.append(unit)
		nodeidx+=1
		#nodes.append([int(items[1]), float(items[8]), float(items[9]), int(items[5]), int(items[6]), int(items[7]),int(items[12]),int(items[13])])
		line = f.readline()
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	##noprint num_units,"units"
	##noprint "reading connectivity ...",
	###id1,id2#####
	node_neighbors = [[]for x in range(len(nodes))]
	if f2!="na":
		#connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]
		f = open(f2)
		line = f.readline()
		line = f.readline()
		links=0
		while line:
			items = line.split(',')
			if len(items)<=2:
				items = line.split()
			if int (items[1]) != int (items[2]):
				id1=int (items[1])
				id2=int (items[2])
				idx1=-1
				idx2=-1
				for i in range(num_units):
					if nodes[i][4]==id1:
						idx1=i
					if nodes[i][4]==id2:
						idx2=i
					if idx1>=0 and idx2>0:
						break
				if idx2 not in node_neighbors[idx1]:
					node_neighbors[idx1].append(idx2)
				if idx1 not in node_neighbors[idx2]:
					node_neighbors[idx2].append(idx1)
				#connectivity[idx1][idx2]=1
				#connectivity[idx2][idx1]=1
				links+=1
			line = f.readline()
		f.close()
	##noprint links,"links"
	num_units=len(nodes)
	facilityCandidate=[]
	facilityCapacity=[]
	facilityCost=[]
	centersID=[]
	print "all data are read! "
	for i in range(num_units):
		if nodes[i][5]>0 or all_units_as_candadate_locations==1:
			facilityCandidate.append(i)
			facilityCapacity.append(nodes[i][5])
			facilityCost.append(nodes[i][7])
			centersID.append(i)
	num_facilityCandidate=len(facilityCandidate)
	num_districts=len(facilityCandidate)
	#facilityCandidate.sort()
	total_supply=sum(facilityCapacity)
	centersID=facilityCandidate[:]
	facility_inclusion_list=[]
	for k in range(num_districts):
		u=facilityCandidate[k]
		if nodes[u][6]==1:
			facility_inclusion_list.append(k)
	print "existing facilities", facility_inclusion_list
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	max_dij=0.0
	print "craeating distance matrix......"
	for i in range(num_units):
		for k in range(num_districts):
			j=facilityCandidate[k]
			d=0.0
			if distance_type==0:
				d2=pow(nodes[i][1]-nodes[j][1],2)
				d2+=pow(nodes[i][2]-nodes[j][2],2)
				d=pow(d2,0.5)
				if distance_meter2kilimeter==1: d /= 1000
			if distance_type==1:
				d=abs(nodes[i][1]-nodes[j][1])
				d+=abs(nodes[i][2]-nodes[j][2])
				if distance_meter2kilimeter==1: d /= 1000
			if distance_type==2: #geo
				d=math.cos(nodes[i][2]/pi)*math.cos(nodes[j][2]/pi)*math.cos((nodes[i][1]-nodes[j][1])/pi)
				d+=math.sin(nodes[i][2]/pi)*math.sin(nodes[j][2]/pi)
				d=math.acos(d)*6371.0
			nodedij[i][k]=d
			if d>max_dij:
				max_dij=d
	''' 
	if len(node_neighbors)>0:
		for i in range(len(nodes)):
			for j in range(len(nodes)):
				if j<=i:
					continue
				if connectivity[i][j]==1:
					node_neighbors[i].append(j)
					node_neighbors[j].append(i)'''

	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	dis=0.0
	for i in range(num_units):
		d=min(nodedij[i])
		dis+=d*nodes[i][3]
	avg_dis_min=dis/total_pop
	#weighted cost from i to k
	
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="M N: "+str(num_districts)+" "+str(num_units)
	arcpy_print(s)
	s="Total demand & supply: "+str(total_pop)+" "+str(total_supply)+" "+str(sum(facilityCost))
	arcpy_print(s)

def read_pcp_file(f1):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global avg_dis_min
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	#nodes.append(node)
	##noprint "reading nodes ...",
	f = open(f1)
	line = f.readline()  #OID    pop    PointX    PointY    fcadidature    fcost    fcapacity
	line=line[0:-1]
	items = line.split()
	n=int(items[0])
	for nodeidx in range(n):
		line = f.readline()
		line=line[0:-1]
		#print line
		items = line.split()
		unit=[nodeidx, float(items[0]), float(items[1]), int(items[3]),nodeidx,int(items[2]),0,0]
		nodes.append(unit)
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	##noprint num_units,"units"
	##noprint "reading connectivity ...",
	connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]

	##noprint links,"links"
	num_units=len(nodes)
	facilityCandidate=[]
	facilityCapacity=[]
	facilityCost=[]
	centersID=[]
	##noprint "all data are read! "
	for i in range(num_units):
		if nodes[i][5]>0:# or all_units_as_candadate_locations==1:
			facilityCandidate.append(i)
			facilityCapacity.append(nodes[i][5])
			facilityCost.append(nodes[i][7])
			centersID.append(i)
	num_facilityCandidate=len(facilityCandidate)
	num_districts=len(facilityCandidate)
	#facilityCandidate.sort()
	total_supply=sum(facilityCapacity)
	centersID=facilityCandidate[:]
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	max_dij=0.0
	for i in range(num_units):
		for k in range(num_districts):
			j=facilityCandidate[k]
			d2=pow(nodes[i][1]-nodes[j][1],2)
			d2+=pow(nodes[i][2]-nodes[j][2],2)
			d=pow(d2,0.5)
			nodedij[i][k]=d
			if d>max_dij:
				max_dij=d

	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	dis=0.0
	for i in range(num_units):
		d=min(nodedij[i])
		dis+=d*nodes[i][3]
	avg_dis_min=dis/total_pop
	#weighted cost from i to k
	
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]

	node_neighbors = [[]for x in range(len(nodes))]
	s="M N: "+str(num_districts)+" "+str(num_units)
	arcpy_print(s)
	s="Total demand & supply: "+str(total_pop)+" "+str(total_supply)
	arcpy_print(s)

def read_cpmp_file(f1):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global avg_dis_min
	global max_num_facility
	global district_info
	node =[0,0,0,0,0,0,0,0,0,0]
	nodes = []
	##noprint "reading nodes ...",
	f = open(f1)
	line = f.readline()  #OID    pop    PointX    PointY    fcadidature    fcost    fcapacity
	line=line[0:-1]
	line=line.strip()
	items = line.split()
	items = line.split()
	n=int(items[0])
	p=int(items[1])
	#max_num_facility=p    
	for nodeidx in range(n):
		line = f.readline()
		line=line[0:-1]
		line=line.strip()
		items = line.split()
		unit=[nodeidx, float(items[0]), float(items[1]), int(items[3]),nodeidx,int(items[2]),0,0]
		if len(items)>=5: unit[6]=float(items[4])
		nodes.append(unit)
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]
	num_districts=num_units
	##noprint links,"links"
	num_units=len(nodes)
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[nodes[x][5] for x in range(num_districts)]
	facilityCost=[nodes[x][6] for x in range(num_districts)]
	centersID=[x for x in range(num_districts)]

	total_supply=sum(facilityCapacity)
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	max_dij=0.0
	for i in range(num_units):
		for j in range(num_districts):
			d2=pow(nodes[i][1]-nodes[j][1],2)
			d2+=pow(nodes[i][2]-nodes[j][2],2)
			d=pow(d2,0.5)
			nodedij[i][j]=d
			if d>max_dij:
				max_dij=d
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]

	node_neighbors = [[]for x in range(len(nodes))]
	s="M N: "+str(num_districts)+" "+str(num_units)
	s+="\nTotal demand: "+str(total_pop)
	s+="\nTotal supply: "+str(total_supply)
	s+="\nTotal cost: "+str(sum(facilityCost))
	arcpy_print(s)
	#s="Total demand & supply: "+str(total_pop)+" "+str(total_supply)

def readfile_ab(f1,f2,f3):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	#nodes.append(node)
	##noprint "reading nodes ...",
	f = open(f1)
	line = f.readline()  #OID   PointX    PointY    demand  sub_region    
	line = f.readline()
	nodeidx=0
	while line:
		line=line[0:-1]
		items = line.split(',')
		if len(items)<=2:
			items = line.split('\t')
		unit=[int(items[0]), float(items[1]), float(items[2]), int(items[3]),0,int(items[4])]
		nodes.append(unit)
		nodeidx+=1
		line = f.readline()
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	f = open(f2)
	line = f.readline()  #OID   PointX    PointY    cap fcost   existing facility
	
	line = f.readline()
	nodeidx=0
	while line:
		line=line[0:-1]
		items = line.split(',')
		if len(items)<=2:
			items = line.split('\t')
		unit=[int(items[0]), float(items[1]), float(items[2]), int(items[3]),int(items[4]),int(items[5])]
		nodes.append(unit)
		if unit[5]==1: facility_inclusion_list.append(nodeidx)
		nodeidx+=1
		line = f.readline()
	f.close()
	print "facility_inclusion_list:", facility_inclusion_list
				
	num_districts=len(nodes)-num_units
	
	facilityCandidate=[num_units+x for x in range(num_districts)]
	facilityCapacity=[nodes[num_units+x][3] for x in range(num_districts)]
	facilityCost=[nodes[num_units+x][4] for x in range(num_districts)]
	centersID=facilityCandidate[:]
	num_facilityCandidate=len(facilityCandidate)

	total_supply=sum(facilityCapacity)
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	if f3=="":
		for i in range(num_units):
			for k in range(num_districts):
				j=num_units+k
				d=0.0
				if distance_type==0:
					d2=pow(nodes[i][1]-nodes[j][1],2)
					d2+=pow(nodes[i][2]-nodes[j][2],2)
					d=pow(d2,0.5)/1000
				if distance_type==1:
					d=abs(nodes[i][1]-nodes[j][1])
					d+=abs(nodes[i][2]-nodes[j][2])
					d/=1000
				if distance_type==2: #geo
					pi=3.14150/180
					d=math.cos(nodes[i][2]/pi)*math.cos(nodes[j][2]/pi)*math.cos((nodes[i][1]-nodes[j][1])/pi)
					d+=math.sin(nodes[i][2]/pi)*math.sin(nodes[j][2]/pi)
					d=math.acos(d)*6371.0
				nodedij[i][k]=d
	else:
		f = open(f3)
		line = f.readline()
		readsuccess=1
		for i in range(num_units):
			line = f.readline()
			items = line.split()
			#len(items)
			for k in range(num_districts):
				d=float(items[k+1])
				nodedij[i][k]=d/1000
		f.close()
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	create_node_neighbors()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="M N: "+str(num_districts)+" "+str(num_units)
	arcpy_print(s)
	s="Demand and supply: "+str(total_pop)+" "+str(sum(facilityCapacity))
	arcpy_print(s)    

def find_nearFacilityFacility():
	global nearFacilityFacility
	nearFacilityFacility=[[] for x in range(num_districts)]
	dkk=[sum(nodedik[x][k]*nodedik[x][k] for x in range(num_units)) for k in range(num_districts)]
	#dkk.sort(key=lambda x:x[1])
	#dlist=[x[0] for x in dkk]
	for k in range(num_districts):
		d=dkk[k]
		dk=[[x,dkk[x]-d] for x in range(num_districts)]
		dk.sort(key=lambda x:x[1])
		del dk[0]
		nearFacilityFacility[k]=[x[0] for x in dk]
	
def find_near_customer():
	global nearCustomer
	global nearCustomers
	if location_problem>=2: 
		nearCustomers=NearFacilityList
		nearCustomer=[x for x in range(num_districts)]
		return
	nearCustomer=[-1 for x in range(num_districts)]
	nearCustomers=[[] for x in range(num_districts)]
	dis=[]
	for k in range(num_districts):
		dis=[ [x,nodedij[x][k]] for x in range(num_units)]
		dis.sort(key=lambda x: x[1])
		nearCustomer[k]=dis[0][0]
		nearCustomers[k]=[x[0] for x in dis]
	   
def initialize_instance():
	global centersID
	global node_groups
	#solution obj 
	global district_info
	global objective_overload
	global objective
	global biobjective
	global all_solutions
	#best solution 
	global best_solution
	global best_centersID
	global best_biobjective
	global best_objective
	global best_objective_overload
	#global best solution 
	global best_solution_global
	global best_centersID_global
	global best_biobjective_global
	global best_objective_global
	global best_overload_global

	if len(node_groups)!=num_units: node_groups=[-1 for x in range(num_units)]
	if len(centersID)!=num_districts: centersID=facilityCandidate[:]
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]

	objective_overload=MAXNUMBER
	obj_balance=MAXNUMBER
	objective=MAXNUMBER
	biobjective=MAXNUMBER
	all_solutions=[]

	#best solution in each start
	best_solution =[] # node_groups[:]
	best_centersID=[]
	best_biobjective=MAXNUMBER
	best_objective=MAXNUMBER
	best_objective_overload = MAXNUMBER

	#global best solution 
	best_solution_global=[]
	best_centersID_global=[]
	best_biobjective_global = MAXNUMBER
	best_objective_global = MAXNUMBER
	best_overload_global = MAXNUMBER
	
#read network distance
def readdistance(dfile):
	global nodedij
	global nodedik
	print "reading distances ..."
	try:
		f = open(dfile)
		#if len(nodedij)!=num_units: 
		nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
		line = f.readline()
		line = f.readline()
		readsuccess=1
		did=[x[4] for x in nodes]
		fid=[x[4] for x in nodes if x[5]>0]
		print fid
		while line:
			items = line.split(',')
			if len(items)<=2:
				items = line.split('\t')
			id1=int (items[1])
			id2=int (items[2])
			if id2 not in fid:
				line = f.readline()
				continue
			idx1=did.index(id1)
			idx2=fid.index(id2)
			nodedij[idx1][idx2]=float(items[3])
			line = f.readline()
		f.close()
		find_NearFacilityList(num_districts)
		find_near_customer() 
		nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
		return 1
	except:
		arcpy_print("Cannot read the distance data file!!!"+dfile)
		return 0

def find_NearFacilityList(nnn):
	global NearFacilityList
	if len(NearFacilityList)>0: return
	NearFacilityList=[]
	n=nnn#num_districts
	if n>num_districts: n=num_districts
	dis=0.0
	print "find_NearFacilityList()",
	for i in range(num_units):
		if i%100==0: print ".",
		fdlist=[ [x,nodedij[i][x]] for x in range(num_districts)]
		fdlist.sort(key=lambda x:x[1])
		flist=[x[0] for x in fdlist[0:n]]
		NearFacilityList.append(flist[:])
	print "\ndata samples"
	for i in range(10):
		u=(i*17)%num_units
		print u,NearFacilityList[u][:10]
		
def SSCFLP_SSCKFLP_model(numf,r,maxtime,mipgap):  #SSCFLP, SSCKFLP
	global node_groups
	global centersID
	global num_districts
	global district_info
	if mip_solver not in mip_solvers:
		return -9
	alpha_coeff=penalty_on_demand
	if alpha_coeff<0.001: alpha_coeff=10000
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	tcosts={}
	for i in range(num_units):
		for j in range(num_districts):
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			tcosts["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
			if r==0:
				costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*travel_distance_weight
			if r==1:
				costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*(random.random()+49.5)/50*travel_distance_weight
			d=nodedij[i][j]
			if envy_service_objective==1 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		if r==0:
			costs["y_" +str(i)]=facilityCost[i]
		if r==1:
			costs["y_" +str(i)]=facilityCost[i]*(random.random()+49.5)/50
	hvariables={}
	#for i in range(num_districts):
	#    hvariables["h_" +str(i)]=pulp.LpVariable("h_" +str(i), 0, None, pulp.LpInteger)

	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	if fixed_cost_obj==1:
		for y in yvariables:
			if costs[y]>0.0:
				obj += costs[y]*yvariables[y]
	#for x in hvariables:
	#    obj+=alpha_coeff*hvariables[x]
	prob += obj

	#con2 1
	s=""
	for k in range(num_districts):
		s+=yvariables["y_" +str(k)]
	if adaptive_number_of_facilities==0:
		prob +=s == numf

	if max_facility_cost>0:
		s=""
		for k in range(num_districts):
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		prob += s <= max_facility_cost

	if cflp_max_service_radius>0:
		s=""
		for k in range(num_districts):
			s += facilityCost[k]*yvariables["y_" +str(k)]
		for x in xvariables:
			s += tcosts[x]*xvariables[x]
		prob += s <= cflp_max_service_radius

	'''s=""
	for i in range(num_districts):
		s+=facilityCapacity[i]*yvariables["y_" +str(i)]    
	prob +=s >= total_pop'''

	#cons 2
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1
	#cons 3
	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]
		#s-=hvariables["h_" +str(k)]
		if facilityMinimumCapacity>0:
			prob+=s >= facilityMinimumCapacity*yvariables["y_" +str(k)]
		s-=facilityCapacity[k] * yvariables["y_" +str(k)]
		#s-=facilityCapacity[k]
		prob+=s <= 0
	   
	#cons 4
	#for k in range(num_districts):
	#    s=hvariables["h_" +str(k)]-100000*yvariables["y_" +str(k)]
	#    prob+=s <= 0
	#cons 5 #can be removed
	'''for i in range(num_units):
		for k in range(num_districts):
			s=xvariables["x_" +str(i) + "_"+ str(k) ]- 100000*yvariables["y_" +str(k)]
			prob+=s <= 0'''

	'''not_opt_cands=[]
	for k in range(num_districts): 
		#print max_exclusion_list[k],biobjective,max_exclusion_list[k]>biobjective+0.0000001
		if max_exclusion_list[k] > biobjective+0.0000001:
			not_opt_cands.append(k)
	for k in not_opt_cands:
		s=yvariables["y_" +str(k)]
		prob+= s==0
	must_opt_cands=[]
	for k in range(num_districts): 
		if max_inclusion_list[k] >biobjective+0.0000001:
			must_opt_cands.append(k)
	for k in must_opt_cands:
		s=yvariables["y_" +str(k)]
		prob+= s==1
	#print biobjective
	s="not_in_opt_cands: "+str(len(not_opt_cands)) + " : " +str(not_opt_cands)
	arcpy_print(s)
	#print "excl",max_exclusion_list
	s1="must_in_opt_cands: "+str(len(must_opt_cands)) + " : " +str(must_opt_cands)
	arcpy_print(s1)
	#print "excl",max_inclusion_list'''

	prob.writeLP("_sscflp.lp")
	initvalues=cflp_mst()
	for x,v in initvalues: 
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#maxSeconds=heuristic_time_limit/multi_start_count/2
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,timeLimit=maxtime,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, warmStart=True,options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=maxtime,warmStart=True,options=[("MIPGap",gap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return prob.status
	sol=[]
	cid=[]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				cid.append(i)
				continue
			if items[0]=='h': continue
			k=int(items[2])
			node_groups[i]=k

	###noprint sol
	#num_districts=len(centersID)
	centersID=facilityCandidate[:]
	for k in range(num_districts):
		if k not in cid:
			centersID[k]=-1
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	update_district_info()
	return prob.status

def cost_dis_CFLP_MIP_model(max_fcost,maxtime,mipgap): 
	global node_groups
	global centersID
	global num_districts
	global district_info
	if mip_solver not in mip_solvers:
		return -9
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	for i in range(num_units):
		for j in range(num_districts):
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
	yvariables={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]

	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	prob += obj

	s=""
	for y in yvariables:
		s += costs[y]*yvariables[y]
	prob +=s <= max_fcost
	s=""
	for i in range(num_districts):
		s+=facilityCapacity[i]*yvariables["y_" +str(i)]    
	prob +=s >= total_pop

	#cons 2
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1
	#cons 3
	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]
		s-=facilityCapacity[k] * yvariables["y_" +str(k)]
		prob+=s <= 0

	prob.writeLP("_bicflp.lp")
	initvalues=cflp_mst()
	for x,v in initvalues: 
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,timeLimit=maxtime,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, warmStart=True,options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=maxtime,warmStart=True,options=[("MIPGap",gap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		return prob.status
	sol=[]
	cid=[]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				cid.append(i)
				continue
			if items[0]=='h': continue
			k=int(items[2])
			node_groups[i]=k
	###noprint sol
	#num_districts=len(centersID)
	centersID=facilityCandidate[:]
	for k in range(num_districts):
		if k not in cid:
			centersID[k]=-1
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	update_district_info()
	return prob.status

def cost_envy_CFLP_MIP_model(max_fcost,mean,maxtime,mipgap): 
	global node_groups
	global centersID
	global num_districts
	global district_info
	if mip_solver not in mip_solvers:
		return -9
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	for i in range(num_units):
		for j in range(num_districts):
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*0.001
			if nodedij[i][j]>mean:
				costs["x_" +str(i)+ "_"+ str(j)]+= nodes[i][3]*(nodedij[i][j]-mean)*(nodedij[i][j]-mean)
	yvariables={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]

	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	prob += obj

	s=""
	for y in yvariables:
		s += costs[y]*yvariables[y]
	prob +=s <= max_fcost

	s=""
	for i in range(num_districts):
		s+=facilityCapacity[i]*yvariables["y_" +str(i)]    
	prob +=s >= total_pop

	#cons 2
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1
	#cons 3
	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]
		s-=facilityCapacity[k] * yvariables["y_" +str(k)]
		prob+=s <= 0

	prob.writeLP("_bicflp.lp")
	initvalues=cflp_mst()
	for x,v in initvalues: 
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,timeLimit=maxtime,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, warmStart=True,options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=maxtime,warmStart=True,options=[("MIPGap",gap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		return prob.status
	sol=[]
	cid=[]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				cid.append(i)
				continue
			if items[0]=='h': continue
			k=int(items[2])
			node_groups[i]=k
	###noprint sol
	#num_districts=len(centersID)
	centersID=facilityCandidate[:]
	for k in range(num_districts):
		if k not in cid:
			centersID[k]=-1
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	update_district_info()
	return prob.status

def cflp_mst():
	vars=[]
	if len(node_groups)<num_units: return vars
	for i in range(num_units):
		k=node_groups[i]
		if k<0: continue
		v='x_'+str(i)+ '_'+ str(k)
		vars.append([v,1])
	for i in range(num_districts):
		if centersID[i]<0:continue
		v='y_'+str(i)
		vars.append([v,1])
	return vars

def location_model_linear_relexation(numf,r,maxtime,mipgap):
	global node_groups
	global centersID
	global num_districts
	global district_info
	if mip_solver not in mip_solvers:
		return -9
	alpha_coeff=penalty_on_demand
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	for i in range(num_units):
		for j in range(num_districts):
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpContinuous)
			if r==0:
				costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
			if r==1:
				costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*(random.random()+19.5)/20
	yvariables={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpContinuous)
		costs["y_" +str(i)]=facilityCost[i]

	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	if fixed_cost_obj==1:
		for y in yvariables:
			if costs[y]>0.0:
				obj += costs[y]*yvariables[y]
	prob += obj

##    for k in facilityCandidate:
##        if nodes[k][6]!=1:
##            continue
##        s=xvariables["x_" +str(k)+ "_"+ str(k)]
##        prob +=s == 1
	
##    for k in facilityCandidate:
##        if nodes[k][6]==1:
##            s=yvariables["y_" +str(k)]
##            prob +=s == 1

	#con2 1
	s=""
	for k in range(num_districts):
		s+=yvariables["y_" +str(k)]
	if adaptive_number_of_facilities==0:
		prob +=s == numf
	#else:
	#    prob +=s == numf
	#cons 2
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1
	#cons 3
	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]
		#s-=hvariables["h_" +str(k)]
		s-=facilityCapacity[k] * yvariables["y_" +str(k)]
		#s-=facilityCapacity[k]
		prob+=s <= 0
	#cons 4
	#for k in range(num_districts):
	#    s=hvariables["h_" +str(k)]-100000*yvariables["y_" +str(k)]
	#    prob+=s <= 0
	#cons 5 #can be removed
	for i in range(num_units):
		for k in range(num_districts):
			s=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]- facilityCapacity[k]*yvariables["y_" +str(k)]
			prob+=s <= 0

	#prob.writeLP("_location.lp")
	#maxSeconds=heuristic_time_limit/multi_start_count/2
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(msg=solver_message,timeLimit=maxtime,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,timeLimit=maxtime)
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,options=[("MIPGap",gap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return prob.status
	sol=[ [x,0.0,[]] for x in range(num_districts)]
	yk=[0.0 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue > 0.0):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				sol[i][1]=v.varValue
				yk[i]=v.varValue
				continue
			if items[0]=='h': continue
			k=int(items[2])
			sol[k][1]+=nodes[i][3]*v.varValue
			sol[k][2].append([i,nodedik[i][k]*v.varValue])
	return yk,sol

def get_cand_locations(dlist,ulist):
	clist=[]
	if len(max_exclusion_list)<=0: 
		clist=[x for x in range(num_districts) if centersID[x]<0 and nearCustomer[x] in ulist]
		random.shuffle(clist)
	else:
		clist=[[x,max_exclusion_list[x]] for x in range(num_districts) if centersID[x]<0 and nearCustomer[x] in ulist and x in potential_facilities]
		clist.sort(key=lambda x:x[1])
		clist=[x[0] for x in clist]
	nc=len(clist)
	nf=len(dlist)
	nu=len(ulist)
	t=time.time()
	mnsize=min(large_neigborhood_maxIJ,num_units*num_districts/10)
	ns=min(nc,mnsize/nu-nf)
	#ns=nc
	if ns<nf: ns=min(nc,nf)
	if ns==nc: return [clist]
	#cloclist=clist[:ns/2]
	#while len(cloclist)<ns:
	#    r=random.random()
	#    idx=int(r**1.5*0.999*(nc-ns/2))
	#    k=clist[ns/2+idx]
	#    if k not in cloclist: cloclist.append(k)
	#cloclist.append(clist[:ns])
	cloclist=[]
	clist1=clist[:ns/2]
	clist2=clist[ns/2:]
	for i in range(5):
		if initial_solution_method!=9:
			random.shuffle(clist)
			cloclist.append(clist[:ns])
		else:
			random.shuffle(clist2)
			cloclist.append(clist1+clist2[:ns/2])
	#print nf,nu,mnsize,nc+nf,ns+nf,
	return cloclist

def get_cand_lscp_locations(dlist,ulist):
	clist=[x for x in range(num_districts) if centersID[x]<0 and nearCustomer[x] in ulist]
	cloclist=[]
	while len(cloclist)<10:
		random.shuffle(clist)
		n=len(dlist)*2
		cloclist.append(clist[:n])
	return cloclist

def get_cand_cflpr_locations(dlist,ulist,r):
	num_f=max_num_facility
	if adaptive_number_of_facilities==1:
		num_f=sum(1 for x in centersID if x>=0)
	nf=len(dlist)
	nu=len(ulist)
	u=-1
	dis=MAXNUMBER
	for i in ulist:
		d=sum(nodedij[i][x] for x in dlist)
		if d<dis:
			dis=d
			u=i
	clist=NearFacilityList[u][:nf*num_districts/num_f]
	clist+=[NearFacilityList[x][0] for x in ulist]
	clist=[x for x in clist if centersID[x]<0]
	clist=list(set(clist))
	random.shuffle(clist)
	nfnu=len(dlist)*len(ulist)
	if nfnu>10000:
		clist=clist[:len(dlist)*1]
	elif nfnu>7000:
		clist=clist[:len(dlist)*2]
	elif nfnu>5000:
		clist=clist[:len(dlist)*3]
	elif nfnu>3500:
		clist=clist[:len(dlist)*5]
	elif nfnu>2500:
		clist=clist[:len(dlist)*7]
	return clist

def get_cand_cflpr_locations2(dlist,ulist,r):
	clist=[]
	for x in dlist:
		u=nearCustomer[x]
		cf=NearFacilityList[u][: int(num_districts/max_num_facility) ]
		cf=[x for x in cf if x not in dlist ]
		random.shuffle(cf)
		clist+=cf[:int(r)]
	clist=list(set(clist))
	return clist

def get_cand_cflpr_locations3(dlist,ulist,r):
	clist=[NearFacilityList[x][0] for x in ulist]
	clist=[x for x in clist if centersID[x]<0]
	clist=list(set(clist))
	random.shuffle(clist)
	n=int(len(dlist)*r)
	return clist[:n]                    

def check_nearest(ulist,klist,maxr): #>2/3
	demand=sum(nodes[i][3] for i in ulist)
	covered=0
	for i in ulist:
		for k in klist:
			if nodedij[i][k]<=maxr:
				covered+=nodes[i][3]
				break
	if covered>demand*2/3: return 1
	return 0

location_sub_model_tabu_list=[]
def location_sub_model(dlist,ulist,mipgap): # SSCFLP,SSCKFLP for subproblem
	global location_sub_model_tabu_list
	alpha_coeff=penalty_on_demand
	prob = pulp.LpProblem("sub_location",pulp.LpMinimize)
	cloclist=get_cand_locations(dlist,ulist)
	centers=[]
	for clist in cloclist:
		tblist=list(set(clist+dlist))
		tblist.sort()
		#print "@",
		if tblist+centersID not in location_sub_model_tabu_list:
			centers=tblist
			break
		#print "+",
	if len(centers)==0: return []
	location_sub_model_tabu_list.append(centers[:]+centersID[:])

	exist_facility=[x for x in range(num_districts) if centersID[x]>=0 and x not in dlist and facilityCapacity[x] > district_info[x][1]]
	#if location_problem==2: exist_facility=[]
	#print dlist,centers,exist_facility
	xvariables={}
	costs={}
	alpha_coeff=penalty_on_demand
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
		for j in exist_facility:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	
	hvariables={}
	for i in centers:
		hvariables["h_" +str(i)]=pulp.LpVariable("h_" +str(i), 0, None, pulp.LpInteger)
		for i in exist_facility:
			hvariables["h_" +str(i)]=pulp.LpVariable("h_" +str(i), 0, None, pulp.LpInteger)
	if location_problem==2:
		for i in centers:
			hvariables["l_" +str(i)]=pulp.LpVariable("l_" +str(i), 0, None, pulp.LpInteger)
		for i in exist_facility:
			hvariables["l_" +str(i)]=pulp.LpVariable("l_" +str(i), 0, None, pulp.LpInteger)

	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	if fixed_cost_obj==1:
		for y in yvariables:
			if costs[y]>0.0:
				obj += costs[y]*yvariables[y]
	for x in hvariables:
		obj+=alpha_coeff*hvariables[x]
	prob += obj


	#con 1
	if adaptive_number_of_facilities==0 or location_problem==2:
		s=""
		for k in centers:
			s+=yvariables["y_" +str(k)]
		prob +=s == len(dlist)

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		for j in exist_facility:
			v="x_" +str(i)+ "_"+ str(j)
			if v in xvariables : s+=xvariables[v]
		prob +=s == 1
	#cons 3
	for k in centers:
		s=""
		for i in ulist:
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]

		s1=s-hvariables["h_" +str(k)]
		s1-=facilityCapacity[k]*(1+pop_deviation) * yvariables["y_" +str(k)]
		prob+=s1 <= 0
		if location_problem==2:
			s2=s+hvariables["l_" +str(k)]
			s2-=facilityCapacity[k]*(1-pop_deviation) * yvariables["y_" +str(k)]
			prob+=s2 >= 0
			
	for k in exist_facility:
		s=""
		for i in ulist:
			v="x_" +str(i)+ "_"+ str(k)
			if v in xvariables: s+=nodes[i][3]*xvariables[v]
		#s-=facilityCapacity[k]
		prob+= s-hvariables["h_" +str(k)] <= facilityCapacity[k]*(1+pop_deviation) - district_info[k][1]
		if location_problem==2:
			prob+= s+hvariables["l_" +str(k)] >= facilityCapacity[k]*(1-pop_deviation) - district_info[k][1]

	#cons 4
	for k in centers:
		s=hvariables["h_" +str(k)]-total_pop*yvariables["y_" +str(k)]
		prob+=s <= 0

	#cons 5 #can be removed
	#for i in ulist:
	#    for k in centers:
	#        s=xvariables["x_" +str(i) + "_"+ str(k) ]- 100000*yvariables["y_" +str(k)]
	#        prob+=s <= 0
	# assign facility unit to itself

	if spatial_contiguity>=1:
		for k in centers:
			u=facilityCandidate[k]
			s=xvariables["x_" +str(u) + "_"+ str(k) ]- yvariables["y_" +str(k)]
			prob+=s == 0

	#prob.writeLP("_sub_location.lp")
	#maxSeconds=heuristic_time_limit/multi_start_count/2
	initvalues=loc_sub_mst(dlist,ulist)
	for x,v in initvalues:
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	gap=mipgap
	if spatial_contiguity>=1: gap=0.005
	timelmt=5
	#solver_message
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=0,gapRel = gap*5,warmStart=True,options=['vnd on','seconds 10', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=0, warmStart=True,timeLimit=5, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=0,warmStart=True, options=[("MIPGap",gap),("TimeLimit",5)] )
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	solx=[0.0 for x in range(num_units)]
	sol=[-1 for x in range(num_units)]
	nlist=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				nlist.append(i)
				continue
			if items[0]=='h': continue
			if items[0]=='l': continue
			x=v.varValue*100
			if x>solx[i]:
				solx[i]=x
				k=int(items[2])
			sol[i]=k
	nc=sum( 1 for x in range(num_districts) if centersID[x]<0 and nearCustomer[x] in ulist and x in potential_facilities)
	#print len(dlist),len(ulist),len(centers),nc+len(dlist),
	# clist=list(set(sol))
	# if -1 in clist: clist.remove(-1)
	# clist = [x for x in clist if x not in centersID]
	# if len(clist)!=len(dlist):
		# prob.writeLP("_sub_location.lp")
		# print dlist,clist,centers
		# print exist_facility
		# print list(set(sol))
		# for v in prob.variables():
			# if v.varValue >= 0.90:
				# if v.name.find("x")>0: continue
				# print v.name, v.varValue
		# exit()
		#prob.writeLP("_sub_location.lp")
	#print [x for x in dlist if x not in nlist],[x for x in nlist if x not in dlist],[x for x in range(num_districts) if x in sol and x not in nlist],
	return sol

def loc_sub_mst(dlist,ulist):
	vars=[]
	for i in ulist:
		k=node_groups[i]
		if k<0: continue
		v='x_'+str(i)+ '_'+ str(k)
		vars.append([v,1])
	for i in dlist:
		if centersID[i]<0:continue
		v='y_'+str(i)
		vars.append([v,1])
	return vars
#uclp with coverage restriction (Nozic 2001)

def uflpr_model(max_radius,cover_pecentage,time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=100000000#facilityCost[i]
	zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	obj=""
	for x in yvariables:
		obj +=costs[x]* yvariables[x]
	#for i in ulist:
	#     for j in centers:
	#        obj+=costs["x_" +str(i)+ "_"+ str(j)]*xvariables["x_" +str(i)+ "_"+ str(j)]
	obj+=100000000*zvariable
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1

	for k in centers:
		for i in ulist:
			s= xvariables["x_" +str(i) + "_"+ str(k) ] - yvariables["y_" +str(k)]
			prob += s <= 0
	s=""
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
	s+=total_pop/100.0*zvariable
	prob += s>=total_pop*cover_pecentage/100
	#prob.writeLP("_uflpr.lp")

	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if v.name=="z": continue
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
	print "model solution:",biobjective,objective_fcost,objective,objective_overload,int(coverdemand*10000/total_pop)/100.0
	all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost])
	all_solutions.sort(key=lambda x:x[0])
	return 1

#d_bar <= mean
def mean_var_mip_model(num_f,capacity,mean,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	xcost={}
	for i in ulist:
		uvariables["u_" +str(i)]=pulp.LpVariable("u_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)

	obj_text= str(total_pop) + " t ^ 2 "
	for i in range(num_units):
		w=str(nodes[i][3])
		w2=str(nodes[i][3]*2)
		obj_text +=" + "+ w +" u_"+str(i) + " ^ 2 - " + w2 + " t *" + " u_"+str(i) 
	obj_text = "[ " +obj_text + " ] / 2 " 
	print "replacing the obj in LP file: _mv.lp"
	print obj_text
	obj=""
	for i in ulist:
		obj +=nodes[i][3]*uvariables["u_" +str(i)]
	prob += obj
	if mean >0:
		prob += tvariable <= mean

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		#nearest assignment   
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	s=""
	for i in ulist:
		s += nodes[i][3]*uvariables["u_" +str(i)]
	prob += s ==total_pop*tvariable

	for i in ulist:
		s=""
		for k in centers:
			s+=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
		prob += s - uvariables["u_" +str(i)] == 0

	prob.writeLP("_mv.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=",v.varValue
				continue
			if items[0]=='d':
				print "d=",v.varValue
				continue
			if items[0]=='u' or items[0]=='v':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

def min_cv_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	vvariables={}
	xcost={}
	for i in ulist:
		vvariables["v_" +str(i)]=pulp.LpVariable("v_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			uvariables["u_" +str(i)+"_"+str(k)]=pulp.LpVariable("u_" +str(i)+"_"+str(k), 0, None, pulp.LpContinuous)
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)
	dvariable=pulp.LpVariable("d", 0, None, pulp.LpContinuous)

	obj_text=str(total_pop) + " d ^ 2 + "
	for i in range(num_units):
		w=str(nodes[i][3])
		w2=str(nodes[i][3]*2)
		obj_text += w +" v_"+str(i) + " ^ 2 - " + w2 + " v_"+str(i) + " * d + "
	obj_text = "[ " +obj_text[:-3] + " ] / 2 " 
	print "===============Replacing the obj in LP file: _mincv.lp==========="
	print "=================and solving the LP file: _mincv.lp ============="

	print obj_text
	obj=""
	for i in ulist:
		obj +=nodes[i][3]*vvariables["v_" +str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		#nearest assignment   
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for k in centers:
		for i in ulist:
			s=uvariables["u_" +str(i)+"_"+str(k)] - bigM*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= 0
	
	s=""
	for i in ulist:
		for k in centers:
			s += nodes[i][3]*uvariables["u_" +str(i)+"_"+str(k)]
	prob += s == total_pop

	for i in ulist:
		for k in centers:
			s=uvariables["u_" +str(i)+"_"+str(k)] - bigM *xvariables["x_" +str(i)+"_"+str(k)] -nodedij[i][k]*tvariable
			prob += s >= -bigM
			s=uvariables["u_" +str(i)+"_"+str(k)] + bigM *xvariables["x_" +str(i)+"_"+str(k)] -nodedij[i][k]*tvariable
			prob += s <= bigM
	for i in ulist:
			s=  ''
			for k in centers:
				s+=uvariables["u_" +str(i)+"_"+str(k)] 
			prob += s - vvariables["v_" +str(i)]  == 0

	prob += dvariable==1.0
	prob.writeLP("_mincv.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=",v.varValue
				continue
			if items[0]=='d':
				print "d=",v.varValue
				continue
			if items[0]=='u' or items[0]=='v':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

#GFFLP: objective: alpha*mean_distance + (1-alpha) * mean_beta_worst_distance_WITH_demand_weight
def FFLP_mip_model(num_f,alpha,beta,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("omp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	beta_demand=beta*total_pop
	print num_f,alpha,beta,time_limit,mipgap                                         
	rvariable=pulp.LpVariable("radius", 0, None, pulp.LpContinuous)
	xvariables={}
	vvariables={}
	xcost={}
	for i in ulist:
		vvariables["v_" +str(i)]=pulp.LpVariable("v_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	uvariable=pulp.LpVariable("u", 0, None, pulp.LpContinuous)

	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in xvariables:
		obj +=alpha*xcost[x]/total_pop*xvariables[x]
	obj += (1-alpha)*beta_demand*uvariable       
	for i in ulist:
		obj+=(1-alpha)*nodes[i][3]*vvariables["v_" +str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for i in ulist:
		s=beta_demand*uvariable + beta_demand*vvariables["v_" +str(i)]
		for k in centers:
			s -= nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s >= 0
	prob.writeLP("_omp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		'''if (v.varValue >= 0.0001):
			items=v.name.split('_')
			if items[0]=='z':
				i=int(items[1])
				k=int(items[2])
				print [v.name,nodes[i][3],nodedij[i][k]],'''
		if v.name=='radius':
			print "beta% radius", v.varValue
		if (v.varValue >= 0.100000001):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				node_groups[i]=int(items[2])
			if items[0]=='v':
				i=int(items[1])
				#print [v.name,nodes[i][3],v.varValue],
			if items[0]=='u':
				print [v.name,v.varValue],
	update_district_info()
	return 1

#KCentdian, FFLP
#alpha * mean + (1-alpha) * mean_K_worst_distance
def KCentdian_mip_model(num_f,alpha,K,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("KCentrum",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	rvariable=pulp.LpVariable("radius", 0, None, pulp.LpContinuous)
	xvariables={}
	uvariables={}
	#zvariables={}
	xcost={}
	for i in ulist:
		uvariables["u_" +str(i)]=pulp.LpVariable("u_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	obj=""
	alpha2=alpha
	if alpha <=0.01: alpha2=0.01
	for x in xvariables:
		obj +=alpha2*xcost[x]/total_pop*xvariables[x]
	for i in ulist:
		obj+= (1-alpha2)*uvariables["u_" +str(i)]
	obj+= (1-alpha2)*K*rvariable
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for i in ulist:
		s = K*rvariable + K*uvariables["u_" +str(i)]   
		for k in centers:
			s -= nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] 
		prob +=s  >= 0

	'''s=""
	for i in ulist:
		for k in centers:
			s+=zvariables["z_" +str(i)+"_"+str(k)]
	prob +=s == K'''
	prob.writeLP("_cpmpr.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.0000001):
			items=v.name.split('_')
			if items[0]=='u':
				i=int(items[1])
				print [v.name,v.varValue],
		if v.name=='radius':
			print "beta% radius", v.varValue, K*v.varValue
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

#1-Centdian
def centdian_mip_model(num_f,alpha, capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]/total_pop
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	z=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	obj=(1-alpha)*z
	for x in xvariables:
		obj+= alpha*xcost[x]*xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for i in ulist:
		for k in centers:
			s=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] - z
			prob +=s <= 0

	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			s-=facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	if capacity==0:
		for i in ulist:
			for k in centers:
				s=xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
				prob += s <= 0

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0

	#prob.writeLP("_pcp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	maxr=0.0
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=='z': continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
				if maxr<nodedij[i][k]:maxr=nodedij[i][k]
	if capacity==0:
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]>=0: 
					node_groups[i]=k
					break
	update_district_info()
	print "MaxR", maxr
	return 1

def MAD_mip_model_original(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	xcost={}
	for i in ulist:
		uvariables["u_" +str(i)]=pulp.LpVariable("u_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)

	obj=""
	for i in ulist:
		obj +=nodes[i][3]*uvariables["u_" +str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					if nodedij[i][j]>nodedij[i][k]:
						s += xvariables["x_" +str(i)+"_"+str(j)]
				if len(s)>1:
					s += yvariables["y_"+str(k)]
					prob +=s  <= 1'''
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	
	s=""
	for x in xvariables:
		s +=xcost[x]* xvariables[x]
	prob += s - total_pop*tvariable == 0

	for i in ulist:
			s=''
			for k in centers:
				s+=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] 
			prob += s - tvariable - uvariables["u_" +str(i)]  <= 0
			prob += s - tvariable + uvariables["u_" +str(i)]  >= 0
	prob.writeLP("_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.1):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=", v.varValue
				continue
			if items[0]=='u':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

##------MinsemiMAD is the same as MinMAD------
def MAD_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	xcost={}
	for i in ulist:
		uvariables["u_" +str(i)]=pulp.LpVariable("u_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)

	obj=""
	for i in ulist:
		obj +=nodes[i][3]*uvariables["u_" +str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					if nodedij[i][j]>nodedij[i][k]:
						s += xvariables["x_" +str(i)+"_"+str(j)]
				if len(s)>1:
					s += yvariables["y_"+str(k)]
					prob +=s  <= 1'''
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	
	s=""
	for x in xvariables:
		s +=xcost[x]* xvariables[x]
	prob += s - total_pop*tvariable == 0

	for i in ulist:
			s=''
			for k in centers:
				s+=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] 
			prob += s - tvariable - uvariables["u_" +str(i)]  <= 0
			#prob += s - tvariable + uvariables["u_" +str(i)]  >= 0
	prob.writeLP("_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.1):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=", v.varValue
				continue
			if items[0]=='u':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1


##-----mean+MAD ------## for testing only
def Mean_MAD_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	xcost={}
	for i in ulist:
		uvariables["u_" +str(i)]=pulp.LpVariable("u_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)

	obj=""
	for i in ulist:
		for k in centers:
			obj+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]    
	for i in ulist:
		obj +=nodes[i][3]*uvariables["u_" +str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					if nodedij[i][j]>nodedij[i][k]:
						s += xvariables["x_" +str(i)+"_"+str(j)]
				if len(s)>1:
					s += yvariables["y_"+str(k)]
					prob +=s  <= 1'''
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	
	s=""
	for x in xvariables:
		s +=xcost[x]* xvariables[x]
	prob += s - total_pop*tvariable == 0

	for i in ulist:
			s=''
			for k in centers:
				s+=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] 
			prob += s - tvariable - uvariables["u_" +str(i)]  <= 0
			#prob += s - tvariable + uvariables["u_" +str(i)]  >= 0
	prob.writeLP("_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.1):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=", v.varValue
				continue
			if items[0]=='u':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

def RMAD_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	vvariables={}
	xcost={}
	for i in ulist:
		vvariables["v_" +str(i)]=pulp.LpVariable("v_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			uvariables["u_" +str(i)+"_"+str(k)]=pulp.LpVariable("u_" +str(i)+"_"+str(k), 0, None, pulp.LpContinuous)
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)

	obj=""
	for i in ulist:
		obj +=nodes[i][3]*vvariables["v_" +str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if capacity==0:
		#nearest assignment   
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0
			s=uvariables["u_" +str(i)+"_"+str(k)] - bigM*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= 0
	
	s=""
	for i in ulist:
		for k in centers:
			s += nodes[i][3]*uvariables["u_" +str(i)+"_"+str(k)]
	prob += s == total_pop

	for i in ulist:
		for k in centers:
			s=uvariables["u_" +str(i)+"_"+str(k)] - bigM *xvariables["x_" +str(i)+"_"+str(k)] -nodedij[i][k]*tvariable
			prob += s >= -bigM
			s=uvariables["u_" +str(i)+"_"+str(k)] + bigM *xvariables["x_" +str(i)+"_"+str(k)] -nodedij[i][k]*tvariable
			prob += s <= bigM
			
	for i in ulist:
			s=''
			for k in centers:
				s+=uvariables["u_" +str(i)+"_"+str(k)] 
			prob += s - 1 - vvariables["v_" +str(i)]  <= 0
			#can be ignored: minSemiMAD!
			#prob += s - 1 + vvariables["v_" +str(i)]  >= 0
	prob.writeLP("_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=",v.varValue
				continue
			if items[0]=='u' or items[0]=='v':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1
def GC_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	vvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
			uvariables["u_" +str(i)+"_"+str(k)]=pulp.LpVariable("u_" +str(i)+"_"+str(k), 0, None, pulp.LpContinuous)
	for i in ulist:
		for j in ulist:
			vvariables["v_" +str(i)+"_"+str(j)]=pulp.LpVariable("v_" +str(i)+"_"+str(j), 0, None, pulp.LpContinuous)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	tvariable=pulp.LpVariable("t", 0, None, pulp.LpContinuous)

	obj=""
	for i in ulist:
		for j in ulist:
			obj +=nodes[i][3]*nodes[j][3]*vvariables["v_" +str(i)+"_"+str(j)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	if capacity==0:
		#nearest assignment   
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	for k in centers:
		for i in ulist:
			s=uvariables["u_" +str(i)+"_"+str(k)] - bigM*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= 0
	
	s=""
	for i in ulist:
		for k in centers:
			s += nodes[i][3]*uvariables["u_" +str(i)+"_"+str(k)]
	prob += s == total_pop

	for i in ulist:
		for k in centers:
			s=uvariables["u_" +str(i)+"_"+str(k)] - bigM *xvariables["x_" +str(i)+"_"+str(k)] -nodedij[i][k]*tvariable
			prob += s >= -bigM
			s=uvariables["u_" +str(i)+"_"+str(k)] + bigM *xvariables["x_" +str(i)+"_"+str(k)] -nodedij[i][k]*tvariable
			prob += s <= bigM   

	for i in ulist:
		for j in ulist:
			s=""
			for k in centers:
				s +=  uvariables["u_" +str(i)+"_"+str(k)] - uvariables["u_" +str(j)+"_"+str(k)]
			prob += s - vvariables["v_" +str(i)+"_"+str(j)]<= 0
			#can be ignored! MinAD==MinSeniAD
			#prob += s + vvariables["v_" +str(i)+"_"+str(j)]>= 0
	prob.writeLP("_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.1):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=", v.varValue
				continue
			if items[0]=='u':
				continue
			if items[0]=='v':
				#print "v",items[1], items[2],v.varValue
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

def AD_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	uvariables={}
	vvariables={}
	xcost={}
	for i in ulist:
		#ui - dev of di        
		uvariables["u_" +str(i)]=pulp.LpVariable("u_" +str(i), 0, None, pulp.LpContinuous)
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	for i in ulist:
		for j in ulist:
			vvariables["v_" +str(i)+"_"+str(j)]=pulp.LpVariable("v_" +str(i)+"_"+str(j), 0, None, pulp.LpContinuous)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for i in ulist:
		for j in ulist:
			obj +=nodes[i][3]*nodes[j][3]*vvariables["v_" +str(i)+"_"+str(j)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	if capacity==0:
		#nearest assignment   
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	for i in ulist:
			s=''
			for k in centers:
				s+=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] 
			prob += s - uvariables["u_" +str(i)]== 0
	for i in ulist:
		for j in ulist:
			s=  uvariables["u_" +str(i)] -uvariables["u_" +str(j)]
			prob += s - vvariables["v_" +str(i)+"_"+str(j)]<= 0
			#can be ignored: minSemiAD!
			#prob += s + vvariables["v_" +str(i)+"_"+str(j)]>= 0
	prob.writeLP("_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.1):
			items=v.name.split('_')
			if items[0]=='t':
				print "t=", v.varValue
				continue
			if items[0]=='u':
				continue
			if items[0]=='v':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1
	
#def pmp_mip_model(max_radius,cover_pecentage,time_limit,mipgap): 
def pmp_mip_model(num_f,radius,cover_percent,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight
			d=nodedij[i][k]
			if envy_service_objective==1 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==10:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			if envy_service_objective==40:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*abs(d-envy_service_distance)

	costs={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		#costs["y_" +str(i)]=100000000#facilityCost[i]
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	#zvariables={}    
	#for i in ulist:
	#    zvariables[i]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			if radius>0 and cover_percent>=100 and nodedij[i][k]>radius: continue
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		if len(s)==0: return 0
		prob +=s  == 1
	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for k in centers:
		s=""
		for i in ulist:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		s-=num_units*yvariables["y_" + str(k)]
		prob +=s <= 0

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0
			
	if cover_percent >0:
		s=""
		for i in ulist:
			for k in centers:
				if nodedij[i][k]>radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  >= total_pop*cover_percent/100

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0


	prob.writeLP("_pmp.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='z':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	'''if envy_service_objective<10 and spatial_contiguity==0:
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k] >=0:
					node_groups[i]=k
					break'''
	update_district_info()
	return 1
	
def EDP_mip_model(num_f,dev,lb,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("edp",pulp.LpMinimize)
	upperCap=(1+dev)*total_pop/num_f
	lowerCap=(1-dev)*total_pop/num_f    
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)
	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj
	if lb>0:
		prob += obj>=lb
	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for k in centers:
		s=""
		for i in ulist:
			s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		prob += s <= upperCap*yvariables["y_" + str(k)]
		prob += s >= lowerCap*yvariables["y_" + str(k)]

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0
	prob.writeLP("_cpmpr.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

#Church et al. (2004)
#model simpified by yfkong (2026)
def RIM_mip_model(r,time_limit,mipgap):
	global centersID
	global node_groups
	prob = pulp.LpProblem("imf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	zvariables={}
	costs={}
	for j in ulist:
		for i in NearFacilityList[j][:r+1]:
			x="x_" +str(i)+"_"+str(j)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
			costs[x]=nodedik[j][i]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		#zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, None, pulp.LpContinuous)
	
	obj=""
	for x in xvariables:
		obj+=costs[x]*xvariables[x]
	'''if capa==1:
		for x in zvariables:
			obj+=penalty*zvariables[x]'''
	prob += obj

	for j in ulist:
		s=""
		for i in NearFacilityList[j][:r+1]:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob += s == 1
	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == r

	for j in ulist:
		for idx in range(r):
				i=NearFacilityList[j][idx]
				s=""
				tlist=[x for x in NearFacilityList[j][idx+1:r+1]]
				if len(tlist)==0: continue
				for k in tlist:
					s+=xvariables["x_" +str(k)+"_"+str(j)]
				s-=yvariables["y_" +str(i)]
				prob += s <= 0

	prob.writeLP("_rim.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[x for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]

	rlist=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				i=int(items[1])
				j=int(items[2])
				node_groups[j]=i
			if items[0]=='y':
				k=int(items[1])
				rlist.append(k)
				centersID[k]=-1                
	rlist.sort()  
	if print_searching_info==1:
		print "attack solution:",pulp.value(prob.objective),rlist
	update_district_info()
	'''for k in range(num_districts):
		if centersID[k]<0: continue
		print district_info[k]'''
	'''print [x for x in range(num_units) if node_groups[x]==17] #flp_c400_30,r=8
	print NearFacilityList[285][:10]
	print [nodedij[285][NearFacilityList[285][x]] for x in range(10)]'''

	return pulp.value(prob.objective),rlist 

#interdiction median problem with fortification
#Scaparra & Church(2008)
#model simpified by yfkong (2026) using LB and UB
def IMF_MC_mip_model(q,r,LB,UB,time_limit,mipgap):
	t_begin=time.time()
	RIM_obj,RIM_List=RIM_mip_model(r,time_limit/3,mipgap)    
	prob = pulp.LpProblem("imf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	rlists=itertools.combinations(centers,r)
	attackList=[]
	comb=0
	comb2=0
	for x in rlists:
		comb += 1
		rlist=list(x)
		wd=0.0
		for j in ulist:
			for k in NearFacilityList[j]:
				if k not in rlist:
					wd+=nodedik[j][k]
					break
		if wd<LB: continue  
		#if wd>UB: continue  
		attackList.append([wd,rlist])
		comb2 += 1
	attackList.sort(key=lambda x:-x[0])
	attackLen=len(attackList)
	if print_searching_info==1:
		print "attack combinations:",comb,"reduced to:",len(attackList) #no improvement

	xvariables={}
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	yvariables={}
	for k in range(attackLen):
		yvariables["y_" +str(k)]=pulp.LpVariable("y_" +str(k), 0, 1, pulp.LpContinuous)
	
	obj=""
	for k in range(attackLen):
		obj+=yvariables["y_" +str(k)]
	prob += obj

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	s=""
	for k in RIM_List:
		s+=xvariables["x_"+str(k)]
	prob +=s  >= 1
	
	for k in range(attackLen):
		wd=attackList[k][0]
		if wd>UB:
			prob += yvariables["y_" +str(k)] == 1
		s=""
		for i in attackList[k][1]:
			s+=xvariables["x_" +str(i)]
		s-=yvariables["y_" +str(k)]
		prob += s >= 0

	for k in range(attackLen-1):
		s=yvariables["y_" +str(k)]-yvariables["y_" +str(k+1)]
		prob += s >= 0
	time_modeling=time.time()-t_begin
	prob.writeLP("_rimf.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "unsolved or infeasible!"
		return 0, 0.0,[],[]
	centersID=[-1 for x in range(num_districts)]
	qlist=[]
	optattack=1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				k=int(items[1])
				if k>optattack:
					optattack=k
	if optattack<len(attackList)-1: 
		optattack+=1
	qlist.sort()  
	alist=attackList[optattack][1]
	alist.sort()  
	#print "time_modeling",time_modeling
	##print "fortification:",qlist
	if print_searching_info==1:
		print "attack:",attackList[optattack][0],alist
	if print_searching_info==1:
		print "solution:",optattack, attackList[optattack][0],qlist,attackList[optattack][1]
	qrlist=list(set(qlist+attackList[optattack][1]))
	if len(qrlist)<len(qlist)+len(attackList[optattack][1]):
		if print_searching_info==1:
			print "incorrect solution!"        
		return 0, 0.0,[],[]
	#print "combinations:",comb,"->",comb2
	return 1, attackList[optattack][0],qlist,attackList[optattack][1]

#random search,tested!
def RIMF_2stage(q,r,maxloops):
	t_begin=time.time()
	solutions=[]
	obj_best=[MAXNUMBER,[],[]]
	ulist=range(num_units)
	centers=range(num_districts)
	Ni=[]
	for k in centers:
		Ni.append([x for x in ulist if NearFacilityList[x][0]==k])

	coverList=[[x,0.0,0.0,0.0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	for j in ulist: #importance for 1-facility interdiction
		k1=NearFacilityList[j][0]
		k2=NearFacilityList[j][1]
		k3=NearFacilityList[j][2]
		k4=NearFacilityList[j][4]
		coverList[k1][1] += nodedik[j][k2]-nodedik[j][k1] 
		coverList[k2][2] += nodedik[j][k3]-nodedik[j][k2] 
		coverList[k3][3] += nodedik[j][k4]-nodedik[j][k3] 
	for x in coverList: 
		x[4]=x[1]+x[2]
		x[5]=x[1]+x[3]
		x[6]=x[3]+x[3]
		x[7]=x[1]+x[2]+x[3]
		#print x
	qrList=[]
	for idx in range(1,8):    
		coverList.sort(key=lambda x:-x[idx])
		qrList.append([x[0] for x in coverList])

	for idx in range(7):
		qlist=qrList[idx][:q]
		qlist.sort()
		obj,rlist=RIM_2nd_model(r,qlist,[], 1000,1.0e-10)
		if obj<obj_best[0]: obj_best=[obj,qlist,rlist]
		print "best",obj_best[0],"init sol.",[obj,qlist,rlist]
	loop=0
	hisList=[]
	hisList.append(str(qlist))
	notimproved=0
	trytimes=0
	while 1:
		if stop_searching==1:
			break
		if trytimes>5000:
			break
		loop+=1
		qlist=obj_best[1][:]
		rlist=obj_best[2][:]
		#if notimproved>maxloops/2:        
		#	rlist+=[x for x in qrList if x not in qlist][:q]
		idx1=random.randint(0,q-1)
		idx2=random.randint(0,len(rlist)-1)
		qlist[idx1]=rlist[idx2]
		qlist.sort()
		if str(qlist) in hisList:
			trytimes+=1
			continue  
		hisList.append(str(qlist))
		notimproved+=1
		obj,rlist=RIM_2nd_model(r,qlist,[], 1000,1.0e-10)
		if obj<obj_best[0]:  
			obj_best[0]=obj 
			obj_best[1]=qlist[:]
			obj_best[2]=rlist[:]    
			notimproved=0
		if print_searching_info==1:
			print "loop:",loop,[idx1,idx2],"best:",obj_best[0], "current:",obj,notimproved,int(time.time()-t_begin)
		if stop_searching==1:
			break    
		if notimproved>=maxloops:
			break
	return obj_best

#random search,tested!
def RIMF_2stage_ILS(q,r,psize,maxloops):
	t_begin=time.time()
	solutions=[]
	obj_best=[MAXNUMBER,[],[]]
	ulist=range(num_units)
	centers=range(num_districts)
	Ni=[]
	for k in centers:
		Ni.append([x for x in ulist if NearFacilityList[x][0]==k])

	coverList=[[x,0.0,0.0,0.0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	for j in ulist: #importance for 1-facility interdiction
		k1=NearFacilityList[j][0]
		k2=NearFacilityList[j][1]
		k3=NearFacilityList[j][2]
		k4=NearFacilityList[j][4]
		coverList[k1][1] += nodedik[j][k2]-nodedik[j][k1] 
		coverList[k2][2] += nodedik[j][k3]-nodedik[j][k2] 
		coverList[k3][3] += nodedik[j][k4]-nodedik[j][k3] 
	for x in coverList: 
		x[4]=x[1]+x[2]
		x[5]=x[1]+x[3]
		x[6]=x[3]+x[3]
		x[7]=x[1]+x[2]+x[3]
		#print x
	qrList=[]
	for idx in range(1,8):    
		coverList.sort(key=lambda x:-x[idx])
		qrList.append([x[0] for x in coverList])
	
	for idx in range(7):
		qlist=qrList[idx][:q]
		qlist.sort()
		obj,rlist=RIM_2nd_model(r,qlist,[], 1000,1.0e-10)
		if obj<obj_best[0]: obj_best=[obj,qlist[:],rlist[:]]
		print "best",obj_best[0],"init sol.",[obj,qlist,rlist]
		solutions.append([obj,qlist[:],rlist[:]])
	loop=0
	hisList=[]
	hisList.append(str(qlist))
	notimproved=0
	trytimes=0
	while 1:
		if stop_searching==1:
			break
		if trytimes>5000:
			break
		loop+=1
		rand=random.random()
		idx=int(pow(rand,1.5)*min(psize,len(solutions)))
		#idx=random.randint(0,min(psize,len(solutions))-1)
		qlist=solutions[idx][1][:]
		rlist=solutions[idx][2][:]
		idx1=random.randint(0,q-1)
		idx2=random.randint(0,len(rlist)-1)
		qlist[idx1]=rlist[idx2]
		qlist.sort()
		if str(qlist) in hisList:
			trytimes+=1
			continue  
		hisList.append(str(qlist))
		notimproved+=1
		obj,rlist=RIM_2nd_model(r,qlist,[], 1000,1.0e-10)
		solutions.append([obj,qlist[:],rlist[:]])
		solutions.sort(key=lambda x:x[0])
		if obj<obj_best[0]:  
			obj_best[0]=obj 
			obj_best[1]=qlist[:]
			obj_best[2]=rlist[:]    
			notimproved=0
		if print_searching_info==1:
			print "loop:",loop,[idx,idx1,idx2],"best:",obj_best[0], "current:",obj,notimproved,int(time.time()-t_begin)
		if stop_searching==1:
			break    
		if notimproved>=maxloops:
			break

	return obj_best

def RIMF_2stage_IE(q,r):
	t_begin=time.time()
	RIMF_node=[]
	ulist=range(num_units)
	obj,rlist=RIM_mip_model(r,1000,1.0e-10)    

	for k in rlist:
		RIMF_node.append([1,[k]])
	loop=0
	hisList=[]
	obj_best=[MAXNUMBER,[],[]]    
	while 1:
		if stop_searching==1:
			break
		branching=0
		leafs=len(RIMF_node)
		for idx in range(leafs):
			if stop_searching==1:
				break    
			if RIMF_node[idx][0]>q: 
				continue
			loop+=1
			obj,rlist=RIM_2nd_model(r,RIMF_node[idx][1],[], 1000,1.0e-10)
			print "loop:",loop,"/",len(RIMF_node),RIMF_node[idx][1],obj,time.time()-t_begin
			if RIMF_node[idx][0]==q: 
				RIMF_node[idx][0]=q+3
				if obj<obj_best[0]:
					obj_best[0]=obj 
					obj_best[1]=RIMF_node[idx][1][:]
					obj_best[2]=rlist[:]    
					print "better solution found:", obj_best
				continue
			'''if obj>objUB:
				RIMF_node[idx][0]=q+2
				continue'''
			RIMF_node[idx][0]=q+1
			for k in rlist:
				nlist=RIMF_node[idx][1]+[k]
				nlist.sort()
				if str(nlist) in hisList:
					continue
				RIMF_node.append([len(nlist),nlist])
				hisList.append(str(nlist))
				branching=1                
		if branching==0:                
			break
	return obj_best

def RIMF_2stage_IE_exch(q,r,mulitstart): 
	#easy to find infeasible solutions better than optimal,due to non-optimal IRM solutions
	t_begin=time.time()
	RIMF_node=[]
	ulist=range(num_units)
	obj,rlist=RIM_mip_model(r,1000,1.0e-10)    

	for k in rlist:
		RIMF_node.append([1,[k]])
	loop=0
	hisList=[]
	obj_best=[MAXNUMBER,[],[]]    
	while 1:
		if stop_searching==1:
			break
		branching=0
		leafs=len(RIMF_node)
		for idx in range(leafs):
			if stop_searching==1:
				break    
			if RIMF_node[idx][0]>q: 
				continue
			loop+=1
			bestRIM=[0.0,[]]
			for k in range(mulitstart):
				obj,rlist=RIM_exch_search(RIMF_node[idx][1],r)
				if obj>bestRIM[0]:
					bestRIM[0]=obj
					bestRIM[1]=rlist[:]
			obj=bestRIM[0]
			rlist=bestRIM[1][:]
			print "loop:",loop,"/",len(RIMF_node),RIMF_node[idx][1],obj,time.time()-t_begin
			if RIMF_node[idx][0]==q: 
				RIMF_node[idx][0]=q+3
				if obj<obj_best[0]:
					obj_best[0]=obj 
					obj_best[1]=RIMF_node[idx][1][:]
					obj_best[2]=rlist[:]    
					print "better solution found:", obj_best
				continue
			'''if obj>objUB:
				RIMF_node[idx][0]=q+2
				continue'''
			RIMF_node[idx][0]=q+1
			for k in rlist:
				nlist=RIMF_node[idx][1]+[k]
				nlist.sort()
				if str(nlist) in hisList:
					continue
				RIMF_node.append([len(nlist),nlist])
				hisList.append(str(nlist))
				branching=1                
		if branching==0:                
			break
	return obj_best

def RIM_2nd_model(r,qlist,rlist,time_limit,mipgap):
	global centersID
	global node_groups
	prob = pulp.LpProblem("imf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	zvariables={}
	costs={}
	for j in ulist:
		for i in NearFacilityList[j][:r+1]:
			x="x_" +str(i)+"_"+str(j)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
			costs[x]=nodedik[j][i]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	
	obj=""
	for x in xvariables:
		obj+=costs[x]*xvariables[x]
	prob += obj

	for j in ulist:
		s=""
		for i in NearFacilityList[j][:r+1]:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob += s == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == r

	for k in qlist:
		prob += yvariables["y_"+str(k)] == 0

	for j in ulist:
		for idx in range(r):
			i=NearFacilityList[j][idx]
			s=""
			tlist=[x for x in NearFacilityList[j][idx+1:r+1]]
			if len(tlist)==0: continue
			for k in tlist:
				s+=xvariables["x_" +str(k)+"_"+str(j)]
			s-=yvariables["y_" +str(i)]
			prob += s <= 0
	#prob.writeLP("_rim.lp")
	if rlist!=[]:
		for k in rlist:
			yvariables["y_"+str(k)].setInitialValue(1)
		for j in ulist:
			for k in NearFacilityList[j]:
				if k not in rlist:
					xvariables["x_" +str(k)+"_"+str(j)].setInitialValue(1)
					break

	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[x for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]

	rlist=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				i=int(items[1])
				j=int(items[2])
				node_groups[j]=i
			if items[0]=='y':
				k=int(items[1])
				rlist.append(k)
				centersID[k]=-1                
	rlist.sort()  
	#print "attack solution:",pulp.value(prob.objective),rlist
	#update_district_info()
	return pulp.value(prob.objective),rlist 

def RIM_exch_search(qlist,r): #testing
	global node_groups
	global centersID
	node_groups=[-1 for x in range(num_units)]
	t_begin=time.time()

	Facility2List=[-1 for x in range(num_units)]
	gainList=[0.0 for x in range(num_districts)] #gian(fi)
	lossList=[0.0 for x in range(num_districts)] #loss(fr)
	extraList=[[0.0 for x in range(num_districts)] for y in range(num_districts)] #extra( fi, fr)
	
	rlist=[x for x in range(num_districts) if x not in qlist]
	random.shuffle(rlist)
	centersID=facilityCandidate[:]
	for x in rlist[:r]:
		centersID[x]=-1
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	#print "init solution", objective,[x for x in range(num_districts) if centersID[x]<0]    
	Renato_update(Facility2List,gainList,lossList,extraList)
	'''print    "Sol2",Facility2List
	print    "gain",gainList
	print    "loss",lossList,extraList
	print    "ex",extraList
	print    node_groups
	print    sum(nodedik[x][node_groups[x]] for x in range(num_units))'''
	sta=1
	while sta>0:
		sta, obj, rlist=RIM_Renato(qlist,Facility2List,gainList,lossList,extraList)
		#print "current solution:", obj, rlist
	return obj, rlist

#random search, better than combined search 
def RIMF_exch_search(q,r,exch_loops,maxloops):
	t_begin=time.time()
	solutions=[]
	obj_best=[MAXNUMBER,[],[]]
	ulist=range(num_units)
	centers=range(num_districts)
	coverList=[[x,0.0,0.0,0.0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	for j in ulist: #importance for 1-facility interdiction
		k1=NearFacilityList[j][0]
		k2=NearFacilityList[j][1]
		k3=NearFacilityList[j][2]
		k4=NearFacilityList[j][4]
		coverList[k1][1] += nodedik[j][k2]-nodedik[j][k1] 
		coverList[k2][2] += nodedik[j][k3]-nodedik[j][k2] 
		coverList[k3][3] += nodedik[j][k4]-nodedik[j][k3] 
	for x in coverList: 
		x[4]=x[1]+x[2]
		x[5]=x[1]+x[3]
		x[6]=x[3]+x[3]
		x[7]=x[1]+x[2]+x[3]
		#print x
	qrList=[]
	for idx in range(1,8):    
		coverList.sort(key=lambda x:-x[idx])
		qrList.append([x[0] for x in coverList])
	for idx in range(7):
		qlist=qrList[idx][:q]
		qlist.sort()
		#obj,rlist=conRIM_Exch(qlist,r,exch_loops)
		if num_units<1000:         
			obj,rlist=RIM_2nd_model(r,qlist,[],1000.0,1.0e-10)
		else:
			obj,rlist=conRIM_Exch(qlist,r,exch_loops*2)
		if obj<obj_best[0]: 
			obj_best=[obj,qlist[:],rlist[:]]
		print "best",obj_best[0],"init sol.",[obj,qlist,rlist]
		solutions.append([obj,qlist[:],rlist[:]])

	loop=0
	notimproved=0
	solutions=[]
	hisList=[]
	trytimes=0    
	while notimproved<maxloops:
		if stop_searching==1:
			break
		if trytimes>=5000:
			break
		qlist=obj_best[1][:]
		rlist=obj_best[2][:]
		old_best=obj_best[0] 
		idx=random.randint(0,13)
		if r>=8 and idx<-7:
			rlist=[x for x in qrList[idx] if x not in qlist]
			rlist=rlist[:q]
		idx1=random.randint(0,q-1)
		idx2=random.randint(0,len(rlist)-1)
		qlist[idx1]=rlist[idx2]  #greedy exchange between qlist and others
		qlist.sort()
		if str(qlist) in hisList:
			trytimes+=1
			continue 
		#hisList.append(str(qlist))
		loop+=1
		trytimes=0    
		notimproved+=1
		obj,rlist=conRIM_Exch(qlist,r,exch_loops)        
		if obj<obj_best[0]: #verify optimality
			if num_units<=1000:
				obj,rlist=RIM_2nd_model(r,qlist,rlist,1000.0,1.0e-10)
			else:
				obj2,rlist2=conRIM_Exch(qlist,r,exch_loops)
				if obj2>obj:
					obj=obj2
					rlist=rlist2
		if obj>1.005*obj_best[0]:
			hisList.append(str(qlist))
		if obj<obj_best[0]*1.005:    
			solutions.append([obj,qlist[:],rlist[:]])
			solutions.sort(key=lambda x:x[0])
		if obj<obj_best[0] and rlist!=obj_best[1]:  
			obj_best[0]=obj 
			obj_best[1]=qlist[:]
			obj_best[2]=rlist[:]    
			notimproved=0
		print "loop:",loop,[idx,idx1,idx2],"best:",obj_best[0], "current:",old_best,"->",obj,notimproved,int(time.time()-t_begin),len(hisList)
		updated=0
		for x in solutions:
			if x[1]==qlist:
			    updated=1
			    if obj>x[0]:
					x[0]=obj
					x[2]=rlist[:]
		if stop_searching==1:
			break    
	#if print_searching_info==1:
	#	print solutions
	return obj_best,solutions

def conRIM_Exch(qlist,r,loops):
	best_sol=[0.0,[]] 
	for i in range(loops):
		obj,rlist=RIM_exch_search(qlist,r)
		if obj>best_sol[0]:
			best_sol[0]=obj
			best_sol[1]=rlist[:]
	return best_sol[0],best_sol[1]

def RIMF_Exch_ILS(q,r,psize,exch_loops,ils_loops):
	t_begin=time.time()
	solutions=[]
	obj_best=[MAXNUMBER,[],[]]
	ulist=range(num_units)
	centers=range(num_districts)
	coverList=[[x,0.0,0.0,0.0,0.0,0.0,0.0,0.0] for x in range(num_districts)]

	for j in ulist: #importance for 1-facility interdiction
		k1=NearFacilityList[j][0]
		k2=NearFacilityList[j][1]
		k3=NearFacilityList[j][2]
		k4=NearFacilityList[j][4]
		coverList[k1][1] += nodedik[j][k2]-nodedik[j][k1] 
		coverList[k2][2] += nodedik[j][k3]-nodedik[j][k2] 
		coverList[k3][3] += nodedik[j][k4]-nodedik[j][k3] 
	for x in coverList: 
		x[4]=x[1]+x[2]
		x[5]=x[1]+x[3]
		x[6]=x[3]+x[3]
		x[7]=x[1]+x[2]+x[3]
	qrList=[]
	for idx in range(1,8):    
		coverList.sort(key=lambda x:-x[idx])
		qrList.append([x[0] for x in coverList])
	for idx in range(7):
		qlist=qrList[idx][:q]
		qlist.sort()
		if num_units>=1000:
			obj,rlist=conRIM_Exch(qlist,r,2*exch_loops)
		else:
			obj,rlist=RIM_2nd_model(r,qlist,[],1000.0,1.0e-10)
		if obj<obj_best[0]: obj_best=[obj,qlist[:],rlist[:]]
		print "best",obj_best[0],"init sol.",[obj,qlist,rlist]
		solutions.append([obj,qlist[:],rlist[:]])
	loop=0
	hisList=[]
	hisList.append(str(qlist))
	notimproved=0
	trytimes=0
	while notimproved<=ils_loops:
		if stop_searching==1:
			break
		notimproved+=1
		loop+=1
		rand=random.random()
		idx=int(pow(rand,1.5)*min(psize,len(solutions)))
		#idx=random.randint(0,min(psize,len(solutions))-1)
		qlist=solutions[idx][1][:]
		rlist=solutions[idx][2][:]
		idx1=random.randint(0,q-1)
		idx3=random.randint(0,13)
		if r>=8 and idx3<-7:
			rlist=[x for x in qrList[idx3] if x not in qlist]
			rlist=rlist[:q]
		idx2=random.randint(0,len(rlist)-1)
		qlist[idx1]=rlist[idx2]
		qlist.sort()
		if str(qlist) in hisList:
			trytimes+=1
			continue 
		obj,rlist=conRIM_Exch(qlist,r,exch_loops)
		if obj<obj_best[0]: #verify optimality
			if num_units<=1000:
				obj,rlist=RIM_2nd_model(r,qlist,rlist,1000.0,1.0e-10)
			else:
				obj2,rlist2=conRIM_Exch(qlist,r,exch_loops)
				if obj2>obj:
					obj=obj2
					rlist=rlist2
		if obj>1.01*solutions[idx][0]:
			hisList.append(str(qlist))
		if obj<obj_best[0]-0.0000001:
			notimproved=0
			obj_best=[obj,qlist[:],rlist[:] ]
		print "loop:",loop,[idx,idx3,idx1,idx2],"best:",obj_best[0], "current:",solutions[idx][0],"->",obj,notimproved,int(time.time()-t_begin),len(hisList)
		solutions.append([obj,qlist[:],rlist[:]])
		solutions.sort(key=lambda x:x[0])
		if stop_searching==1:
			break    
	return obj_best, solutions

def RIM_Renato(Qlist,Facility2List,gainList,lossList,extraList):
	global node_groups
	global centersID
	kiList=[x for x in range(num_districts) if centersID[x]<0]
	krList=[x for x in range(num_districts) if centersID[x]>=0 and x not in Qlist]
	#print Qlist,krList

	random.shuffle(kiList)
	random.shuffle(krList)
	improved=0
	bestSwap=[]
	for kr in krList:
		for ki in kiList:
			profit=gainList[ki]-lossList[kr]+extraList[ki][kr]
			#print ki,kr,profit
			if profit<0: 
				bestSwap.append([ki,kr,profit])
	if bestSwap==[]:
		return 0, objective,[x for x in range(num_districts) if centersID[x]<0]
	bestSwap.sort(key=lambda x:x[2])
	idx=0
	'''if len(bestSwap)>2:
		idx=random.randint(0,2)'''
	bestki=bestSwap[idx][0]
	bestkr=bestSwap[idx][1]
	bestprofit=bestSwap[idx][2]
	if bestkr in Qlist:
		print "warning: bestki in Qlist",Qlist,bestSwap[0],krList  
	#print "solution update",bestki,bestkr,bestprofit,gainList[bestki],lossList[bestkr],extraList[bestki][bestkr],facilityCost[bestkr]-facilityCost[bestki],        
	# undo  gainList,lossList,extraList
	alist=[i for i in range(num_units) if node_groups[i]==bestkr or Facility2List[i]==bestkr or nodedij[i][bestki]<nodedij[i][Facility2List[i]] ]
	for i in alist:
		k1=node_groups[i]
		k2=Facility2List[i]
		d1=nodedik[i][k1]
		d2=nodedik[i][k2]
		lossList[k1]-=d2-d1
		for k in range(num_districts):
			if centersID[k]>=0: continue
			d=nodedik[i][k]
			if d<d2:
				gainList[k]-=max(0,d1-d)
				extraList[k][k1]-=d2-max(d,d1)
	#update solution
	centersID[bestkr]=-1
	centersID[bestki]=facilityCandidate[bestki]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
		k=node_groups[i]
		if k!=bestkr:
			if nodedij[i][k]>nodedij[i][bestki]: 
				node_groups[i]=bestki
		else:
			k=Facility2List[i]
			if nodedij[i][bestki]<nodedij[i][k]:
				k=bestki
			node_groups[i]=k
	#obj1=biobjective
	update_district_info()
	'''obj2=biobjective
	print "swap improve and ptofit:",obj1-obj2,bestprofit'''
	#update  Facility2List,gainList,lossList,extraList
	for i in range(num_units):
		k1=node_groups[i]
		for k2 in NearFacilityList[i]:
			if centersID[k2]<0: continue
			if k2==k1: continue
			Facility2List[i]=k2
			break
	for i in alist:
		k1=node_groups[i]
		k2=Facility2List[i]
		d1=nodedik[i][k1]
		d2=nodedik[i][k2]
		lossList[k1]+=d2-d1
		for k in range(num_districts):
			if centersID[k]>=0: continue
			d=nodedik[i][k]
			if d<d2:
				gainList[k]+=max(0,d1-d)
				extraList[k][k1]+=d2-max(d,d1)
	#Renato_update(Facility2List,gainList,lossList,extraList)
	update_district_info()
	improved=1
	return improved,objective,[x for x in range(num_districts) if centersID[x]<0]

#model simpified by yfkong (2026) and used to binary search
def IMF_BS_mip_model(q,r,RIM_List,attackList,LB,UB,time_limit,mipgap):
	t_begin=time.time()
	prob = pulp.LpProblem("imf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	yvariables={}
	for k in range(LB,UB):
		yvariables["y_" +str(k)]=pulp.LpVariable("y_" +str(k), 0, 1, pulp.LpContinuous)
	
	obj=""
	for k in range(LB,UB):
		obj+=yvariables["y_" +str(k)]
	prob += obj

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	s=""
	for k in RIM_List:
		s+=xvariables["x_"+str(k)]
	prob +=s  >= 1
	
	for k in range(UB):
		s=""
		for i in attackList[k][1]:
			s+=xvariables["x_" +str(i)]
		if k<LB:
			prob += s >= 1
		else:
			s-=yvariables["y_" +str(k)]
			prob += s >= 0
	for k in range(LB,UB-1):
		s=yvariables["y_" +str(k)]-yvariables["y_" +str(k+1)]
		prob += s >= 0
	time_modeling=time.time()-t_begin
	prob.writeLP("_rimf.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		#print "incorrect! try to increase the UB!"
		return -2, 0.0,[],[]
	centersID=[-1 for x in range(num_districts)]
	qlist=[]
	optattack=LB
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				k=int(items[1])
				if k>optattack:
					optattack=k
	if optattack<len(attackList)-1: 
		optattack+=1
	qlist.sort()  
	alist=attackList[optattack][1]
	alist.sort()  
	#print "time_modeling",time_modeling
	##print "fortification:",qlist
	#print "attack:",attackList[optattack][0],alist
	#print "solution:",optattack,"/",len(attackList), attackList[optattack][0],qlist,attackList[optattack][1]
	qrlist=list(set(qlist+attackList[optattack][1]))
	if len(qrlist)<len(qlist)+len(attackList[optattack][1]):
		#print "infeasible!",attackList[optattack][0],qlist,attackList[optattack][1]        
		return -1,attackList[optattack][0],qlist,attackList[optattack][1]        
		#return -1, 0.0,[],[]
	return 1, attackList[optattack][0],qlist,attackList[optattack][1]

#Church et al. (2004)
def RIC_mip_model(Qlist,r,maxr,time_limit,mipgap):
	global centersID
	global node_groups
	prob = pulp.LpProblem("imf",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	costs={}
	nlist=[]
	for j in ulist:
		ilist=[]
		for i in centers:
			if nodedij[j][i]<=maxr:
				ilist.append(i)
		nlist.append(ilist)
	'''for i in centers:
		ilist=[]
		for j in ulist:
			if nodedij[j][i]<=maxr:
				ilist.append(j)
		print i,ilist,sum(nodes[x][3] for x in ilist)'''

	for j in ulist:
		x="x_" +str(j)
		xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
		costs[x]=nodes[j][3]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	
	obj=""
	for x in xvariables:
		obj+=costs[x]*xvariables[x]
	prob += obj


	s=""
	for i in centers:
		if i in Qlist: continue
		s+=yvariables["y_"+str(i)]
	prob +=s  == r

	for j in ulist:
		for i in nlist[j]:
			s=xvariables["x_" +str(j)]+yvariables["y_" +str(i)]
			prob += s >= 1

	prob.writeLP("_ric.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	sol=[0 for x in range(num_units)]
	rlist=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='y':
				k=int(items[1])
				rlist.append(k)
				centersID[k]=-1                
			if items[0]=='x':
				k=int(items[1])
				sol[k]=nodes[k][3]  
	obj=pulp.value(prob.objective)

	
	rlist.sort()  
	#print "demand covered:",obj, "attack list:",rlist
	#print "covered list:",sum(sol)#,sol
	return obj,rlist

#RICF: r-interdiction covering problem with fortification (RICF)
# Roboredo et al. (2019)
#RICF-UB
def RICF_mip_model(q,r,radius,objLB,objUB,time_limit,mipgap):
	t_begin=time.time()
	RIC_obj,RIC_list= RIC_mip_model([],r,radius,time_limit,mipgap)
	prob = pulp.LpProblem("ricf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
		Nj.append(ilist)
	Cj=[len(Nj[x]) for x in range(num_units)]
	#print "Nj",Nj  
	xvariables={}
	yvariables={}
	for j in ulist:
		yvariables["y_" +str(j)]=pulp.LpVariable("y_" +str(j), 0, 1, pulp.LpContinuous)
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=zvariable
	prob += obj

	#prob += zvariable >= objLB

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	s=""
	for k in RIC_list:
		s+=xvariables["x_"+str(k)]
	prob +=s  >= 1

	for j in ulist:
		s=yvariables["y_"+str(j)]
		for k in Nj[j]:
			s-=xvariables["x_"+str(k)]
		prob +=s  <= 0
	for j in ulist:
		for k in Nj[j]:
			s=xvariables["x_"+str(k)]
			s-=yvariables["y_"+str(j)]
			prob +=s  <= 0
	rlists=itertools.combinations(centers,r)
	rlists_back=[]
	comb=0
	comb2=0

	for x in rlists:
		comb+=1
		rlist=list(x)
		Cj2=Cj[:]
		for k in rlist:
			for j in Ni[k]:
				Cj2[j]-=1
		covered=sum(nodes[x][3] for x in range(num_units) if Cj2[x]>0)
		if covered > objUB: continue 
	
		rlists_back.append(rlist)#print rlist
		if covered<objLB:
			s=""
			for k in rlist:
				s += xvariables["x_"+str(k)]
			prob +=s  >= 1
			continue

		s=zvariable
		for j in ulist:
			if Cj2[j]==0: s-=nodes[j][3]*yvariables["y_"+str(j)]
		prob +=s  <= covered
		comb2+=1
		if comb%10000==0: print ".",
	print         
	print "Set K:", comb,"->",comb2 #no improvement             
	time_modeling=time.time()-t_begin
	#prob.writeLP("_ricf.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return -2,0,[],[]
	centersID=[-1 for x in range(num_districts)]
	
	qlist=[]
	cover=[0 for x in range(num_units)]
	covered_obj=0
	for v in prob.variables():
		if v.varValue >= 0.90:
			if v.name=="z":
				covered_obj=int(v.varValue)
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				j=int(items[1])
				cover[j]=1
	obj=int(pulp.value(prob.objective)+0.000001)
	#print "time_modeling",time_modeling
	#print "demand ocvered:",obj,covered_obj
	qlist.sort()  
	#print "fortification:",qlist

	max_idx=-1
	max_cover=0
	for idx in range(len(rlists_back)):
		rlist=rlists_back[idx][:]
		sta=0
		for k in rlist:
			if k in qlist:
				sta=1    
				break
		if sta==1: continue
		covered=0
		for j in ulist:
			nlist=Nj[j][:]
			for x in rlist:
				if x in nlist: 
					nlist.remove(x)
			if len(nlist)>0:
				covered+=nodes[j][3]
		#if covered==obj:
		#   print rlist,covered
		if covered>obj: continue
		if covered>max_cover:
			max_cover=covered
			max_idx=idx
	#print "Combination:", comb,comb2 #no improvement               
	print "solution",obj, qlist, rlists_back[max_idx]
	if max_idx <0:
		return -1, obj, qlist, []
	return 1, obj, qlist, rlists_back[max_idx]

#by yfkong (2026)
#RICF-LB&UB
def RICF_MC_mip_model(q,r,radius,objLB,objUB,time_limit,mipgap):
	t_begin=time.time()
	RIC_obj,RIC_list= RIC_mip_model([],r,radius,time_limit,mipgap)
	prob = pulp.LpProblem("icf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	Nj=[]
	for j in ulist:
		ilist=[]
		for k in centers:
			if nodedij[j][k]<=radius:
				ilist.append(k)
		Nj.append(ilist)

	rlists=itertools.combinations(range(num_districts),r)
	Klist=[]
	cmbs=0    
	for x in rlists:
		cmbs+=1    
		rlist=list(x)
		covered=0
		for j in range(num_units):
			t=0
			for k in Nj[j]:
				if k not in rlist:
					t=1
					break
			if t==1:
				covered+=nodes[j][3]
		if covered > objUB: continue 
		Klist.append([covered,rlist])#print rlist
	Klist.sort(key=lambda x:x[0])
	UB=len(Klist)
	LB=0
	for idx in range(UB):
		if Klist[idx][0]>=objLB:
			break        
		LB=idx
	print "Set K:", cmbs, "->", UB, "L=",LB,"U=",UB#, Klist[:10],Klist[-1]
	
	xvariables={}
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	yvariables={}
	for k in range(LB,UB):
		yvariables["y_" +str(k)]=pulp.LpVariable("y_" +str(k), 0, 1, pulp.LpContinuous)
	
	obj=""
	for k in range(LB,UB):
		obj+=yvariables["y_" +str(k)]
	prob += obj

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	'''s=""
	for k in RIC_list:
		s+=xvariables["x_"+str(k)]
	prob +=s  >= 1'''
	
	for k in range(UB):
		s=""
		for i in Klist[k][1]:
			s+=xvariables["x_" +str(i)]
		if k<LB:
			prob += s >= 1
		else:
			s-=yvariables["y_" +str(k)]
			prob += s >= 0
	for k in range(LB,UB-1):
		s=yvariables["y_" +str(k)]-yvariables["y_" +str(k+1)]
		prob += s >= 0
	time_modeling=time.time()-t_begin
	prob.writeLP("_sub_ricf.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		#print "incorrect! try to increase the UB!"
		return -2, 0.0,[],[]
	centersID=[-1 for x in range(num_districts)]
	qlist=[]
	optattack=1
	attackList=Klist
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				k=int(items[1])
				if k>optattack:
					optattack=k
	if optattack<len(attackList)-1: 
		optattack+=1
	qlist.sort()  
	alist=attackList[optattack][1]
	alist.sort()  
	#print "time_modeling",time_modeling
	##print "fortification:",qlist
	#print "attack:",attackList[optattack][0],alist
	#print "solution:",optattack,"/",len(attackList), attackList[optattack][0],qlist,attackList[optattack][1]
	qrlist=list(set(qlist+attackList[optattack][1]))
	if len(qrlist)<len(qlist)+len(attackList[optattack][1]):
		#print "infeasible!",attackList[optattack][0],qlist,attackList[optattack][1]        
		return -1,attackList[optattack][0],qlist,attackList[optattack][1]        
		#return -1, 0.0,[],[]
	return 1, attackList[optattack][0],qlist,attackList[optattack][1]

#RICF-UB for binary search
def RICF_BS_mip_model(q,r,radius,Nj,RIC_list,Klist,objLB,UB,time_limit,mipgap):
	t_begin=time.time()
	prob = pulp.LpProblem("_ricf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	yvariables={}
	for j in ulist:
		yvariables["y_" +str(j)]=pulp.LpVariable("y_" +str(j), 0, 1, pulp.LpContinuous)
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=zvariable
	prob += obj

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	#prob += zvariable >= objLB

	'''s=""
	for k in RIC_list:
		s+=xvariables["x_"+str(k)]
	prob +=s  >= 1'''

	for j in ulist:
		s=yvariables["y_"+str(j)]
		for k in Nj[j]:
			s-=xvariables["x_"+str(k)]
		prob +=s  <= 0
	for j in ulist:
		for k in Nj[j]:
			s=xvariables["x_"+str(k)]
			s-=yvariables["y_"+str(j)]
			prob +=s  <= 0
	for S in Klist[:UB]:
		rlist=S[1]
		if S[0]<objLB:
			s=""
			for k in rlist:
				s += xvariables["x_"+str(k)]
			prob +=s  >= 1
			continue
		cover=[0 for x in range(num_units)]
		for j in ulist:
			t=0
			for k in Nj[j]:
				if k not in rlist:
					t=1
					break
			if t==0:
				cover[j]=1
		s=""
		for j in ulist:
			s+=cover[j]*nodes[j][3]*yvariables["y_"+str(j)]
		prob +=s  >= zvariable - S[0]
			
	time_modeling=time.time()-t_begin
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return -2,0,[],[]
	centersID=[-1 for x in range(num_districts)]
	
	qlist=[]
	cover=[0 for x in range(num_units)]
	covered_obj=0
	for v in prob.variables():
		if v.varValue >= 0.90:
			if v.name=="z":
				covered_obj=int(v.varValue)
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				j=int(items[1])
				cover[j]=1
	obj=int(pulp.value(prob.objective))
	#print "time_modeling",time_modeling
	#print "demand ocvered:",obj,covered_obj
	qlist.sort()  
	#print "fortification:",qlist
	'''if obj > Klist[UB][1]:
		return -1, obj, qlist, []'''
	max_idx=-1
	max_cover=0
	for idx in range(UB):
		rlist=Klist[idx][1]
		if len(list(set(rlist+qlist)))<q+r:
			continue
		if Klist[idx][0]==obj:
			max_cover=Klist[idx][0]
			max_idx=idx
			break
	#print "Combination:", comb,comb2 #no improvement               
	#print "solution",obj, qlist, rlists_back[max_idx]
	if max_idx <0:
		return -1, obj, qlist, rlist
	return 1, obj, qlist, Klist[max_idx][1]

#RICF-UB for binary search
def RICF_BS2_mip_model(q,r,radius,Nj,RIC_list,Klist,LB,UB,time_limit,mipgap):
	t_begin=time.time()
	prob = pulp.LpProblem("_ricf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	yvariables={}
	for j in ulist:
		yvariables["y_" +str(j)]=pulp.LpVariable("y_" +str(j), 0, 1, pulp.LpContinuous)
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=zvariable
	prob += obj

	#prob += zvariable <= Klist[UB-1][1]
	#prob += zvariable >= Klist[LB][1]

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	for j in ulist:
		s=yvariables["y_"+str(j)]
		for k in Nj[j]:
			s-=xvariables["x_"+str(k)]
		prob +=s  <= 0
	for j in ulist:
		for k in Nj[j]:
			s=xvariables["x_"+str(k)]
			s-=yvariables["y_"+str(j)]
			prob +=s  <= 0
	for S in Klist[:LB]:
		rlist=S[1]
		s=""
		for k in rlist:
			s += xvariables["x_"+str(k)]
		prob +=s  >= 1
	for S in Klist[LB:UB]:
		rlist=S[1]
		cover=[0 for x in range(num_units)]
		for j in ulist:
			t=0
			for k in Nj[j]:
				if k not in rlist:
					t=1
					break
			if t==0:
				cover[j]=1
		s=""
		for j in ulist:
			s+=cover[j]*nodes[j][3]*yvariables["y_"+str(j)]
		prob +=s  >= zvariable - S[0]

	time_modeling=time.time()-t_begin
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return -2,0,[],[]
	centersID=[-1 for x in range(num_districts)]
	
	qlist=[]
	cover=[0 for x in range(num_units)]
	covered_obj=0
	for v in prob.variables():
		if v.varValue >= 0.90:
			if v.name=="z":
				covered_obj=int(v.varValue)
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				j=int(items[1])
				cover[j]=1
	obj=int(pulp.value(prob.objective))
	#print "time_modeling",time_modeling
	#print "demand ocvered:",obj,covered_obj
	qlist.sort()  
	#print "fortification:",qlist
	'''if obj > Klist[UB][1]:
		return -1, obj, qlist, []'''
	max_idx=-1
	max_cover=0
	for idx in range(UB):
		rlist=Klist[idx][1]
		if len(list(set(rlist+qlist)))<q+r:
			continue
		if Klist[idx][0]==obj:
			max_cover=Klist[idx][0]
			max_idx=idx
			break
	#print "Combination:", comb,comb2 #no improvement               
	#print "solution",obj, qlist, rlists_back[max_idx]
	if max_idx <0:
		return -1, obj, qlist, []
	return 1, obj, qlist, Klist[max_idx][1]

#model simpified by yfkong (2026) and used to binary search
#RICF-MC-LB&UB
def RICF_bound_mip_model(q,r,RIC_List,attackList,LB,UB,time_limit,mipgap):
	t_begin=time.time()
	prob = pulp.LpProblem("imf",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	for k in centers:
		xvariables["x_" +str(k)]=pulp.LpVariable("x_" +str(k), 0, 1, pulp.LpBinary)
	yvariables={}
	for k in range(LB,UB):
		yvariables["y_" +str(k)]=pulp.LpVariable("y_" +str(k), 0, 1, pulp.LpContinuous)
	
	obj=""
	for k in range(LB,UB):
		obj+=yvariables["y_" +str(k)]
	prob += obj

	#prob += yvariables["y_" +str(LB)] == 1  
	#prob += yvariables["y_" +str(UB-1)] == 0

	s=""
	for k in centers:
		s+=xvariables["x_"+str(k)]
	prob +=s  == q

	'''s=""
	for k in RIC_List:
		s+=xvariables["x_"+str(k)]
	prob +=s  >= 1'''
	
	for k in range(UB):
		s=""
		for i in attackList[k][1]:
			s+=xvariables["x_" +str(i)]
		if k<LB: 
			prob += s >= 1 #infeasible for original problem 
		else:
			s-=yvariables["y_" +str(k)]
			prob += s >= 0
	for k in range(LB,UB-1):
		s=yvariables["y_" +str(k)]-yvariables["y_" +str(k+1)]
		prob += s >= 0
	time_modeling=time.time()-t_begin
	prob.writeLP("_sub_ricf.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit),("MIPFocus",1)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		#print "incorrect! try to increase the UB!"
		return -2, 0.0,[],[]
	centersID=[-1 for x in range(num_districts)]
	qlist=[]
	optattack=1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				k=int(items[1])
				qlist.append(k)
			if items[0]=='y':
				k=int(items[1])
				if k>optattack:
					optattack=k
	if optattack<len(attackList)-1: 
		optattack+=1
	qlist.sort()  
	alist=attackList[optattack][1]
	alist.sort()  
	#print "time_modeling",time_modeling
	##print "fortification:",qlist
	#print "attack:",attackList[optattack][0],alist
	#print "solution:",optattack,"/",len(attackList), attackList[optattack][0],qlist,attackList[optattack][1]
	qrlist=list(set(qlist+attackList[optattack][1]))
	if len(qrlist)<len(qlist)+len(attackList[optattack][1]):
		#print "infeasible!",attackList[optattack][0],qlist,attackList[optattack][1]        
		return -1,attackList[optattack][0],qlist,attackList[optattack][1]        
		#return -1, 0.0,[],[]
	return 1, attackList[optattack][0],qlist,attackList[optattack][1]

#based on the observation that important facilities will be protected
def RICF_2stage(q,r,radius,loops):
	t_begin=time.time()
	RIC_obj,RIC_list= RIC_mip_model([],r,radius,heuristic_time_limit,1.0e-10)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)

	coverList=[[x,0,0,0] for x in range(num_districts)]

	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
				coverList[k][1] += nodes[j][3] #demand covered if used
		Nj.append(ilist)
	MaxCover=sum(nodes[x][3] for x in range(num_units) if Nj[x]!=[])
	print "original covering", MaxCover
	for k in centers:
		for j in ulist:
			#if Nj[j]==[k]:
			if len(Nj[j])<=2 and k in Nj[j]:
				coverList[k][2] += nodes[j][3] #servcie lost if not used

	for k1 in centers:
		for k2 in centers:
			if k1==k2: continue            
			for j in ulist:
				if Nj[j]==[k1,k2] or Nj[j]==[k2,k1]:
					coverList[k1][3] += nodes[j][3] #servcie lost if not used
					coverList[k2][3] += nodes[j][3] #servcie lost if not used

	coverList.sort(key=lambda x:-x[2])
	qrList=[x[0] for x in coverList]
	#qlist=qrList[:q]
	#qlist.sort()

	qlist=[]
	M=max(q,num_districts/4)
	covered=[0 for x in ulist]
	while len(qlist)<q:
		clist=[x for x in qrList if x not in qlist]
		#clist=clist[:M]
		bestc=[]
		for k in clist:
			sumw=sum(nodes[x][3] for x in Ni[k] if covered[x]==0)
			bestc.append([k,sumw])
		bestc.sort(key=lambda x:-x[1])
		rand=random.random()
		idx=0#int(pow(rand,2)*3)
		k=bestc[idx][0]
		qlist.append(k)
		for x in Ni[k]: covered[x]=1
	qlist.sort()
	
	obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
	obj_best=[obj,qlist[:],rlist[:]]
	if print_searching_info==1:
		print "init sol.",obj_best
	hisList=[]
	hisList.append(str(qlist))
	
	loop=0
	notimproved=0
	try_times=0    
	while 1:
		if stop_searching==1:
			break    
		qlist=obj_best[1][:]
		rlist=obj_best[2][:]

		klist1=qlist[:]
		idx1=random.randint(0,q-1)
		klist2=rlist[:]
		#klist3=[x for x in qrList if x not in qlist and x not in rlist]
		#klist2 += klist3 #[:r]
		idx2=random.randint(0,r-1)
		klist1[idx1]=klist2[idx2]
		qlist=klist1[:]
		qlist.sort()
		sta=0
		try_times+=1    
		if try_times>=5000:    
			break
		'''for k in qlist:
			if k in RIC_list:
				sta=1    
				break
		if sta==0: 
			continue'''
		if str(qlist) in hisList:
			continue
		hisList.append(str(qlist))
		try_times=0    
		loop+=1
		notimproved+=1
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		#if len(rlist)<r: print [idx1,idx2,qlist, rlist]

		qlist.sort()    
		if obj>obj_best[0]: 
			obj_best[0]=obj 
			obj_best[1]=qlist[:]
			obj_best[2]=rlist[:]    
			notimproved=0
		if print_searching_info==1:
			print "loop:",loop,"best:",obj_best[0], "current:",obj,notimproved,int(time.time()-t_begin)
		if notimproved>=loops:
			break
		if stop_searching==1:
			break    
	#print len(hisList),hisList
	return obj_best

#based on the observation that important facilities will be protected
def RICF_2stage_ils(q,r,radius,psize,loops):
	t_begin=time.time()
	population=[]    
	obj_best=[0,[],[]]
	RIC_obj,RIC_list= RIC_mip_model([],r,radius,heuristic_time_limit,1.0e-10)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	coverList=[[x,0,0,0,0,0] for x in range(num_districts)]
	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
				coverList[k][1] += nodes[j][3] #demand covered if used
		Nj.append(ilist)
	MaxCover=sum(nodes[x][3] for x in range(num_units) if Nj[x]!=[])
	print "original covering", MaxCover
	#print "Covering damands:", Ni
	for k in centers:
		for j in ulist:
			if Nj[j]==[k]:
				coverList[k][2] += nodes[j][3] #servcie lost if not used
			if len(Nj[j])<=2 and k in Nj[j]:
				coverList[k][3] += nodes[j][3] #servcie lost if not used
			if len(Nj[j])<=3 and k in Nj[j]:
				coverList[k][4] += nodes[j][3] #servcie lost if not used
			if len(Nj[j])<=4 and k in Nj[j]:
				coverList[k][5] += nodes[j][3] #servcie lost if not used
	impList=[[x,0.0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	for k in range(1,6):
		maxv=max(x[k] for x in coverList)
		if maxv==0: continue
		for i in range(num_districts):
			impList[i][k]=1.0*coverList[i][k]/maxv
	print "k: covering, lost, lost2, r-score, 50%-score",impList

	coverList=[[x,0.0] for x in range(num_districts)]
	for k in range(num_districts):
		score=impList[k][2:6]
		print k,score,max(score),sum(score)
		coverList[k][1]=max(score)+sum(score)
	print coverList
	coverList.sort(key=lambda x:-x[1])
	qrList=[x[0] for x in coverList]


	'''while len(population)<psize:
		qlist=[]
		covered=[0 for x in ulist]
		while len(qlist)<q:
			clist=[x for x in qrList if x not in qlist]
			#clist=clist[:q]
			bestc=[]
			for k in clist:
				sumw=sum(nodes[x][3] for x in Ni[k] if covered[x]==0)
				bestc.append([k,sumw])
			bestc.sort(key=lambda x:-x[1])
			idx=random.randint(0,3)
			k=bestc[idx][0]
			qlist.append(k)
			for x in Ni[k]: covered[x]=1
		qlist.sort()
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		if obj>obj_best[0]:
			obj_best=[obj,qlist[:],rlist[:]]
		population.append([obj,qlist[:],rlist[:]])
		if print_searching_info==1:
			print "init sol.",obj_best'''
	while len(population)<psize:
		qlist=[]
		covered=[0 for x in ulist]
		while len(qlist)<q:
			clist=[x for x in qrList if x not in qlist]
			clist=clist[:q+r]
			random.shuffle(clist)
			clist=clist[:q+r/2]
			bestc=[]
			for k in clist:
				sumw=sum(nodes[x][3] for x in Ni[k] if covered[x]==0)
				bestc.append([k,sumw])
			bestc.sort(key=lambda x:-x[1])
			k=bestc[0][0]
			qlist.append(k)
			for x in Ni[k]: covered[x]=1
		qlist.sort()
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		if obj>obj_best[0]:
			obj_best=[obj,qlist[:],rlist[:]]
		population.append([obj,qlist[:],rlist[:]])
		if print_searching_info==1:
			print "init sol.",obj_best

	hisList=[]
	hisList.append(str(qlist))
	
	loop=0
	notimproved=0
	try_times=0    
	while 1:
		if stop_searching==1:
			break    
		idx=random.randint(0,min(psize,len(population)-1) )       
		qlist=population[idx][1][:]
		rlist=population[idx][2][:]

		klist1=qlist[:]
		idx1=random.randint(0,q-1)
		#klist2=[x for x in qrList if x not in qlist]
		#rand=random.random()
		#idx2=int(pow(rand,1.5)*len(klist2))  #good solution(gap=0.13),but slow
		idx2=random.randint(0,r-1)
		klist1[idx1]=rlist[idx2]
		qlist=klist1[:]
		qlist.sort()
		sta=0
		try_times+=1    
		if try_times>=5000:    
			break
		for k in qlist:
			if k in RIC_list:
				sta=1    
				break
		if sta==0: 
			continue
		if str(qlist) in hisList:
			continue
		hisList.append(str(qlist))
		try_times=0    
		loop+=1
		notimproved+=1
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		#if len(rlist)<r: print [idx1,idx2,qlist, rlist]
		qlist.sort()    
		if obj>0.9*obj_best[0]:       
			population.append([obj,qlist[:],rlist[:]])
		if obj>obj_best[0]: 
			obj_best[0]=obj 
			obj_best[1]=qlist[:]
			obj_best[2]=rlist[:]    
			notimproved=0
		if print_searching_info==1:
			print "loop:",loop,[idx1,idx2],"best:",obj_best[0], "current:",population[idx][0],'->',obj,notimproved,int(time.time()-t_begin)
		if notimproved>=loops:
			break
		if stop_searching==1:
			break    
		population.sort(key=lambda x:-x[0])
	#print len(hisList),hisList
	return obj_best

#based on the observation that important facilities will be protected
def RICF_init(q,r,radius,L):
	t0=time.time()
	population=[]    
	obj_best=[0,[],[]]
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	coverList=[[x,0,0,0,0,0,0,0,0,0,0,0,0] for x in range(num_districts)]
	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
		Nj.append(ilist)
	for k in centers:
		for j in ulist:
			if Nj[j]==[k]:
				coverList[k][1] += nodes[j][3] #servcie covering lost if not used
			if len(Nj[j])==2 and k in Nj[j]:
				coverList[k][2] += nodes[j][3] #servcie covering lost if not used
			if len(Nj[j])==3 and k in Nj[j]:
				coverList[k][3] += nodes[j][3] #servcie covering lost if not used
			if len(Nj[j])==4 and k in Nj[j]:
				coverList[k][4] += nodes[j][3] #servcie covering lost if not used
	max1=max(x[1] for x in coverList)
	max2=max(x[2] for x in coverList)
	max3=max(x[3] for x in coverList)
	max4=max(x[4] for x in coverList)
	max1=max(max1,1)    
	max2=max(max2,1)    
	max3=max(max3,1)    
	max4=max(max4,1)    
	for k in centers:
		coverList[k][5] = coverList[k][1]+coverList[k][2]
		coverList[k][6] = coverList[k][1]+coverList[k][2]+coverList[k][3]
		coverList[k][7] = coverList[k][1]+coverList[k][2]+coverList[k][3]+coverList[k][4]
		coverList[k][8] = coverList[k][1]*1.0/max1+coverList[k][2]*1.0/max2
		coverList[k][9] = coverList[k][8]+coverList[k][3]/max3
		coverList[k][10] = coverList[k][9]+coverList[k][4]/max4

	'''for k in centers:
		obj,rlist=RICF_2nd_model(r,Nj,[k],10,1.0e-10)
		coverList[k][8]=-obj'''
	print "=========facility importance============="
	for x in coverList: print x
	obj_best=[0,[],[]]
	for loop in range(10):
		idx=loop%7+1
		coverList.sort(key=lambda x:-x[idx])
		qrList=[x[0] for x in coverList]
		qlist=[]
		covered=[0 for x in ulist]
		while len(qlist)<q:
			clist=[x for x in qrList if x not in qlist]
			clist=clist[:L]
			bestc=[-1,0.0]
			for k in clist:
				sumw=sum(nodes[x][3] for x in Ni[k] if covered[x]==0)
				if sumw>bestc[1]: bestc=[k,sumw]
			k=bestc[0]
			qlist.append(k)
			for x in Ni[k]: covered[x]=1
		qlist.sort()
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		if obj>obj_best[0]:
			obj_best=[obj,qlist[:],rlist[:]]
		print "best",obj_best[0],"init sol.",loop,obj,qlist,rlist
	print "solution:",obj_best,time.time()-t0

#based on the observation that important facilities will be protected
def RICF_greedy(q,r,radius,psize,loops):
	t_begin=time.time()
	population=[]    
	obj_best=[0,[],[]]
	RIC_obj,RIC_list= RIC_mip_model([],r,radius,heuristic_time_limit,1.0e-10)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	coverList=[[x,0,0,0,0,0,0,0,0] for x in range(num_districts)]
	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
		Nj.append(ilist)
	MaxCover=sum(nodes[x][3] for x in range(num_units) if Nj[x]!=[])
	print "original covering", MaxCover
	#print "Covering damands:", Ni
	for k in centers:
		for j in ulist:
			if Nj[j]==[k]:
				coverList[k][1] += nodes[j][3] #servcie covering lost if not used
			if len(Nj[j])==2 and k in Nj[j]:
				coverList[k][2] += nodes[j][3] #servcie covering lost if not used
			if len(Nj[j])==3 and k in Nj[j]:
				coverList[k][3] += nodes[j][3] #servcie covering lost if not used
			if len(Nj[j])==4 and k in Nj[j]:
				coverList[k][4] += nodes[j][3] #servcie covering lost if not used
	for k in centers:
		coverList[k][5] = coverList[k][1]+coverList[k][2]
		coverList[k][6] = coverList[k][1]+coverList[k][2]+coverList[k][3]
		coverList[k][7] = coverList[k][1]+coverList[k][2]+coverList[k][3]+coverList[k][4]

	for loop in range(psize*7):
		idx=loop%7+1
		coverList.sort(key=lambda x:-x[idx])
		qrList=[x[0] for x in coverList]
		qlist=[]
		covered=[0 for x in ulist]
		while len(qlist)<q:
			clist=[x for x in qrList if x not in qlist]
			clist=clist[:q+r]
			random.shuffle(clist)
			clist=clist[:q+r/2]
			bestc=[]
			for k in clist:
				sumw=sum(nodes[x][3] for x in Ni[k] if covered[x]==0)
				bestc.append([k,sumw])
			bestc.sort(key=lambda x:-x[1])
			k=random.randint(0,1)            
			k=bestc[k][0]
			qlist.append(k)
			for x in Ni[k]: covered[x]=1
		qlist.sort()
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		if obj>obj_best[0]:
			obj_best=[obj,qlist[:],rlist[:]]
		new_sol=1
		for x in population:
			if x[1]==qlist:
				new_sol=0
				break
		if new_sol==1:
			population.append([obj,qlist[:],rlist[:]])
		if print_searching_info==1:
			print "best",obj_best[0],"init sol.",loop,obj,qlist,rlist
	population.sort(key=lambda x:-x[0])
	hisList=[]
	hisList.append(str(qlist))
	
	loop=0
	notimproved=0
	try_times=0    
	while 1:
		try_times+=1    
		if try_times>5000:
			break    
		if stop_searching==1:
			break    
		idx=random.randint(0,min(psize,len(population))-1 )       
		qlist=population[idx][1][:]
		rlist=population[idx][2][:]
	 
		idx3=random.randint(0,13)
		if idx3<7:
			coverList.sort(key=lambda x:-x[idx3+1])
			qrList=[x[0] for x in coverList]
			rlist=qrList[:q]
		idx1=random.randint(0,q-1)
		idx2=random.randint(0,len(rlist)-1)
		qlist[idx1]=rlist[idx2]
		qlist.sort()
		if str(qlist) in hisList:
			continue
		hisList.append(str(qlist))
		try_times=0    
		loop+=1
		notimproved+=1
		obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
		#if len(rlist)<r: print [idx1,idx2,qlist, rlist]
		qlist.sort()    
		if obj>0.99*obj_best[0]:       
			new_sol=1
			for x in population:
				if x[1]==qlist:
					new_sol=0
					break
			if new_sol==1:
				population.append([obj,qlist[:],rlist[:]])
			#population.append([obj,qlist[:],rlist[:]])
		if obj>obj_best[0]: 
			obj_best[0]=obj 
			obj_best[1]=qlist[:]
			obj_best[2]=rlist[:]    
			notimproved=0
		if print_searching_info==1:
			print "loop:",loop,[idx,idx3,idx1,idx2],"best:",obj_best[0], "current:",population[idx][0],'->',obj,notimproved,int(time.time()-t_begin)
		if notimproved>=loops:
			break
		if stop_searching==1:
			break    
		population.sort(key=lambda x:-x[0])
	#print len(hisList),hisList
	return obj_best

#RIC for RICF
def RICF_2nd_model(r,Nj,qlist,time_limit,mipgap):
	t_begin=time.time()
	prob = pulp.LpProblem("ricf_sub",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	svariables={}
	tvariables={}
	for k in centers:
		svariables["s_" +str(k)]=pulp.LpVariable("s_" +str(k), 0, 1, pulp.LpBinary)
	for j in ulist:
		tvariables["t_" +str(j)]=pulp.LpVariable("t_" +str(j), 0, 1, pulp.LpBinary)

	obj=""
	for j in ulist:
		obj+= nodes[j][3]*tvariables["t_" +str(j)]   
	prob += obj
	s=""
	for k in centers:
		if k in qlist: continue
		s+=svariables["s_"+str(k)]
	prob +=s  == r

	for j in ulist:
		for k in Nj[j]:
			s=svariables["s_"+str(k)] + tvariables["t_"+str(j)]
			prob +=s  >= 1
	for k in qlist:
		prob += svariables["s_"+str(k)] == 0
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		return []
	rlist=[]
	for v in prob.variables():
		if v.varValue >= 0.90:
			items=v.name.split('_')
			if items[0]=='s':
				k=int(items[1])
				rlist.append(k)
	obj=int(pulp.value(prob.objective)+0.0001)
	rlist.sort()  
	return obj, rlist

def RICF_Exch_search(q,r,radius,loops,loops2):
	t_begin=time.time()
	RIC_obj,RIC_list= RIC_mip_model([],r,radius,heuristic_time_limit,1.0e-10)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)

	coverList=[[x,0,0,0] for x in range(num_districts)]

	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
				coverList[k][1] += nodes[j][3] #demand covered if used
		Nj.append(ilist)
	MaxCover=sum(nodes[x][3] for x in range(num_units) if Nj[x]!=[])
	Nc=[len(Nj[x]) for x in range(num_units)]

	for k in centers:
		for j in ulist:
			#if Nj[j]==[k]:
			if len(Nj[j])<=2 and k in Nj[j]:
				coverList[k][2] += nodes[j][3] #servcie lost if not used

	for k1 in centers:
		for k2 in centers:
			if k1==k2: continue            
			for j in ulist:
				if Nj[j]==[k1,k2] or Nj[j]==[k2,k1]:
					coverList[k1][3] += nodes[j][3] #servcie lost if not used
					coverList[k2][3] += nodes[j][3] #servcie lost if not used

	coverList.sort(key=lambda x:-x[2])
	qrList=[x[0] for x in coverList]
	qlist=qrList[:q]
	qlist.sort()
	
	obj,rlist=RICF_2nd_model(r,Nj,qlist,heuristic_time_limit,1.0e-10)
	obj_best=[obj,qlist[:],rlist[:]]
	if print_searching_info==1:
		print "init sol.",obj_best
	hisList=[]
	hisList.append(str(qlist))
	solutions=[]	
	loop=0
	notimproved=0
	try_times=0    
	while 1:
		if stop_searching==1:
			break    
		qlist=obj_best[1][:]
		rlist=obj_best[2][:]

		klist1=obj_best[1][:]
		idx1=random.randint(0,q-1)
		klist2=obj_best[2][:]
		idx2=random.randint(0,r-1)
		klist1[idx1]=klist2[idx2]
		qlist=klist1[:]
		qlist.sort()
		sta=0
		try_times+=1    
		if try_times>=5000:    
			break
		'''for k in qlist:
			if k in RIC_list:
				sta=1    
				break
		if sta==0: 
			continue
		if str(qlist) in hisList:
			continue
		hisList.append(str(qlist))'''
		try_times=0    
		loop+=1
		notimproved+=1
		best_RIC=[1.0e10,[]]
		for idx3 in range(loops):
			obj,rlist=RIC_Exch(qlist[:],[],r,Ni,Nc)
			if obj<best_RIC[0]:
				best_RIC[0]=obj
				best_RIC[1]=rlist[:]
		qlist.sort()    
		if best_RIC[0]>obj_best[0]: 
			obj_best[0]=best_RIC[0]
			obj_best[1]=qlist[:]
			obj_best[2]=best_RIC[1][:]    
			solutions.append(copy.deepcopy(obj_best))                    
			notimproved = 0
		if print_searching_info==1:
			print "loop:",loop,"best:",obj_best[0], "current:",obj,notimproved,int(time.time()-t_begin)
		if notimproved>=loops2:
			break
		if stop_searching==1:
			break    
	#print len(hisList),hisList
	solutions.sort(key=lambda x:-x[0])                    
	print "final step to verify solutions...."
	#print solutions    
	tabu=[]
	best_RICF=[0,[],[]]
	for x in solutions:
		if x[0]<best_RICF[0]:break
		if x[1] in tabu: continue
		tabu.append(x[1][:])
		obj,rlist=RICF_2nd_model(r,Nj,x[1],10,1.0e-10)
		#obj,rlist=RICF_MIP_model(x[1],r,Nj,10,1.0e-10)
	  
		if obj>best_RICF[0]:	
			best_RICF[0]=obj	
			best_RICF[1]=x[1][:]
			best_RICF[2]=rlist[:]	
		print "best",best_RICF,"current",x,"->",[obj, x[1], rlist]
	return best_RICF
		
#based on the observation that important facilities will be protected
def RICF_Exch_search2(q,r,radius,loops):
	t_begin=time.time()
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	coverList=[[x,0,0,0] for x in range(num_districts)]

	Nj=[]
	Ni=[[] for x in range(num_districts)]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=radius:
				ilist.append(k)
				Ni[k].append(j)
				coverList[k][1] += nodes[j][3] #demand covered if used
		Nj.append(ilist)
	Nc=[len(Nj[x]) for x in range(num_units)]
	MaxCover=sum(nodes[x][3] for x in range(num_units) if Nj[x]!=[])

	for k in centers:
		for j in ulist:
			if len(Nj[j])<=2 and k in Nj[j]:
				coverList[k][2] += nodes[j][3] #servcie lost if not used

	coverList.sort(key=lambda x:-x[2])
	qrList=[x[0] for x in coverList]
	qlist=qrList[:q]
	qlist.sort()
	obj,rlist=RIC_Exch(qlist,[],r,Ni,Nc)	
	obj_best=[0.0,qlist,rlist]
	hisList=[]
	hisList.append(str(qlist))
	solutions=[]
	loop=0
	while 1:
		if stop_searching==1:
			break    
		qlist=obj_best[1][:]
		rlist=obj_best[2][:]
		klist1=[x for x in qrList if x in qlist]
		klist1.reverse()
		klist2=[x for x in qrList if x in rlist]
		klist3=[x for x in qrList if x not in qlist and x not in rlist]
		klist2+=klist3 #[:max(r,num_districts/2-r)]
		#klist2=[x for x in qrList if x not in qlist]
		random.shuffle(klist1)
		random.shuffle(klist2)

		improved=0
		for idx1 in range(q):
			for idx2 in range(len(klist2)):
				qlist=klist1[:]
				k=klist2[idx2]
				qlist[idx1]=k
				qlist.sort()
				'''if str(qlist) in hisList:
					continue
				hisList.append(str(qlist))'''
				loop+=1
				best_RIC=[1.0e10,[]]
				for idx3 in range(loops):
					obj,rlist=RIC_Exch(qlist,[],r,Ni,Nc)
					if obj<best_RIC[0]:
						best_RIC[0]=obj
						best_RIC[1]=rlist[:]
				if best_RIC[0]<obj_best[0] and qlist==obj_best[1]: 
					print best_RIC, obj_best[1]
					obj_best[0]=best_RIC[0]
					obj_best[1]=qlist[:]
					obj_best[2]=best_RIC[1][:]    
					improved=1
					solutions.append(copy.deepcopy(obj_best))                    
				if best_RIC[0]>obj_best[0] and qlist!=obj_best[1]: 
					obj_best[0]=best_RIC[0]
					obj_best[1]=qlist[:]
					obj_best[2]=best_RIC[1][:]    
					improved=1
					solutions.append(copy.deepcopy(obj_best))                    
				if print_searching_info==1:
					print "loop:",loop,idx1,idx2,"best:",obj_best[0], "current:",best_RIC[0],improved,int(time.time()-t_begin),len(solutions)
				if stop_searching==1:
					break   
				if improved==1:
					break
			if improved==1:
				break
			if stop_searching==1:
				break    
		if improved==0:
			break
		if stop_searching==1:
			break    
	solutions.sort(key=lambda x:-x[0])                    
	print "final step to verify solutions...."
	#print solutions    
	tabu=[]
	best_RICF=[0,[],[]]
	for x in solutions:
		if x[0]<best_RICF[0]:break
		if x[1] in tabu: continue
		tabu.append(x[1][:])
		obj,rlist=RICF_2nd_model(r,Nj,x[1],10,1.0e-10)
		#obj,rlist=RICF_MIP_model(x[1],r,Nj,10,1.0e-10)
	  
		if obj>best_RICF[0]:	
			best_RICF[0]=obj	
			best_RICF[1]=x[1][:]
			best_RICF[2]=rlist[:]	
		print "best",best_RICF,"current",x,"->",[obj, x[1], rlist]

	#print len(hisList),hisList
	return best_RICF

def RIC_Exch(Qlist,Rlist,r,Ni,Nc):
	best_rlist=Rlist[:]
	if Rlist==[]:
		klist=[x for x in range(num_districts) if x not in Qlist]
		random.shuffle(klist)
		best_rlist=klist[:r]
	covered=Nc[:]
	for k in best_rlist:
		for j in Ni[k]:
			covered[j] -= 1
	improved=1
	while improved:
		krList=best_rlist
		kiList=[x for x in range(num_districts) if x not in Qlist and x not in krList]
		random.shuffle(krList)
		random.shuffle(kiList)
		improved=0
		best_exch=[]
		for kr in krList:
			for ki in kiList:
				ulist1=[x for x in Ni[kr] if x not in Ni[ki] ] #units that got a facility
				ulist2=[x for x in Ni[ki] if x not in Ni[kr] ] #units that lost a facility
				#ulist3=[x for x in Ni[kr] if x in Ni[ki] ]  #lost and got
				profit = sum(nodes[j][3] for j in ulist1 if covered[j]==0)
				profit -= sum(nodes[j][3] for j in ulist2 if covered[j]==1)
				if profit<0:#best_exch[0]:
					best_exch.append([profit,kr,ki])
					improved=1
					#break  #first / best acceptance 
		if improved==1:
			idx=0
			best_exch.sort(key=lambda x:x[0])
			'''if len(best_exch)>=4:
				idx=random.randint(0,3)'''
			kr=best_exch[idx][1]
			ki=best_exch[idx][2]
			best_rlist.remove(kr)
			best_rlist.append(ki)
			ulist1=[x for x in Ni[kr] if x not in Ni[ki] ] #units that got a facility
			ulist2=[x for x in Ni[ki] if x not in Ni[kr] ] #units that lost a facility
			for j in ulist1:
				covered[j] +=1
			for j in ulist2:
				covered[j] -=1
	obj = sum(nodes[x][3] for x in range(num_units) if covered[x]>=1)
	best_rlist.sort()
	#print profit, covered
	return obj, best_rlist

def RICF_IE(q,r,maxR):
	t_begin=time.time()
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	Nj=[]
	for j in range(num_units):
		ilist=[]
		for k in range(num_districts):
			if nodedij[j][k]<=maxR:
				ilist.append(k)
		Nj.append(ilist)
	
	RICF_node=[]
	obj,rlist=RIC_mip_model([],r,maxR,1000,1.0e-10)    
	for k in rlist:
		RICF_node.append([1,[k]])
	loop=0
	hisList=[]
	obj_best=[0.0,[],[]]    
	while 1:
		if stop_searching==1:
			break
		branching=0
		leafs=len(RICF_node)
		for idx in range(leafs):
			if stop_searching==1:
				break    
			if RICF_node[idx][0]>q: 
				continue
			loop+=1
			obj,rlist=RICF_2nd_model(r,Nj,RICF_node[idx][1],1000,1.0e-10)
			print "loop:",loop,"/",len(RICF_node),RICF_node[idx][1],obj,time.time()-t_begin
			if RICF_node[idx][0]==q: 
				RICF_node[idx][0]=q+3
				if obj>obj_best[0]:
					obj_best[0]=obj 
					obj_best[1]=RICF_node[idx][1][:]
					obj_best[2]=rlist[:]    
					print "better solution found:", obj_best
				continue
			RICF_node[idx][0]=q+1
			for k in rlist:
				nlist=RICF_node[idx][1]+[k]
				nlist.sort()
				if str(nlist) in hisList:
					continue
				RICF_node.append([len(nlist),nlist])
				hisList.append(str(nlist))
				branching=1                
		if branching==0:                
			break
	return obj_best

#R-covering reliableFL, RUFL(Cui etal.,2010, OR)
#tested by instances
def RFLP_mip_model(frate,Clevel, penalty,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)

	xvariables={}
	yvariables={}
	pvariables={}
	wvariables={}
	wcosts={}
	for j in ulist:
		for r in range(Clevel+1):
			for i in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(r)
				p="p_" +str(i)+"_"+str(j)+"_"+str(r)
				w="w_" +str(i)+"_"+str(j)+"_"+str(r)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
				pvariables[p]=pulp.LpVariable(p, 0, 1, pulp.LpContinuous)
				wvariables[w]=pulp.LpVariable(w, 0, 1, pulp.LpContinuous)
				wcosts[w]=nodedik[j][i]
			x="x_" +str(num_districts)+"_"+str(j)+"_"+str(r)
			p="p_" +str(num_districts)+"_"+str(j)+"_"+str(r)
			w="w_" +str(num_districts)+"_"+str(j)+"_"+str(r)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
			pvariables[p]=pulp.LpVariable(p, 0, 1, pulp.LpContinuous)
			wvariables[w]=pulp.LpVariable(w, 0, 1, pulp.LpContinuous)
			wcosts[w]=nodes[j][3]*penalty

	ycosts={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycosts["y_" +str(i)] = facilityCost[i]
	
	obj=""
	for x in yvariables:
		obj+=ycosts[x]*yvariables[x]
	for x in wvariables:
		obj+=wcosts[x]*wvariables[x]
	prob += obj
	
	for j in ulist: #assignment
		for r in range(Clevel): 
			s=""
			for i in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
			prob +=s  == 1  

	for j in ulist: # assign to open facility
		for r in range(Clevel): 
			for i in centers:
				s=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]-yvariables["y_" +str(i)]
				prob +=s  <= 0  

	for i in centers:# assign to open facility
		for j in ulist:
			s=""
			for r in range(Clevel): 
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
			s-=yvariables["y_" +str(i)]
			prob +=s  <= 0

	for j in ulist: #virtual facility must be an open facility
		s=xvariables["x_" +str(num_districts)+"_"+str(j)+"_"+str(Clevel)]
		prob +=s  == 1

	for i in centers: #pijk at level 0
		for j in ulist:
			s=pvariables["p_" +str(i)+"_"+str(j)+"_0"]
			prob +=s  == 1-frate[i]
	
	for i in centers:
		for j in ulist:
			for r in range(Clevel+1): 
				s=wvariables["w_" +str(i)+"_"+str(j)+"_"+str(r)]
				prob +=s  <= pvariables["p_" +str(i)+"_"+str(j)+"_"+str(r)]
				s=wvariables["w_" +str(i)+"_"+str(j)+"_"+str(r)]
				prob +=s  <= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
				s=wvariables["w_" +str(i)+"_"+str(j)+"_"+str(r)]
				s-=pvariables["p_" +str(i)+"_"+str(j)+"_"+str(r)]
				s-=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
				prob +=s >=-1
	for j in ulist:
		for r in range(Clevel+1): 
				s=wvariables["w_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				prob +=s  <= pvariables["p_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				s=wvariables["w_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				prob +=s  <= xvariables["x_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				s=wvariables["w_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				s-=pvariables["p_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				s-=xvariables["x_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
				prob +=s >=-1

	for i in centers:
		for j in ulist:
			for r in range(1,Clevel+1): 
				s=pvariables["p_" +str(i)+"_"+str(j)+"_"+str(r)]
				for k in centers: 
					s-=(1-frate[i])*frate[k]/(1-frate[k])*wvariables["w_" +str(k)+"_"+str(j)+"_"+str(r-1)]
				prob +=s ==0
					
	for j in ulist:
		for r in range(1,Clevel+1): 
			s=pvariables["p_" +str(num_districts)+"_"+str(j)+"_"+str(r)]
			for k in centers: 
				  s-=frate[k]/(1-frate[k])*wvariables["w_" +str(k)+"_"+str(j)+"_"+str(r-1)]
			prob +=s ==0

	prob.writeLP("_rflp.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	xsol=[]
	psol=[]
	wsol=[]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	solution=[[-1 for x in range(Clevel+1)]for y in range(num_units+1) ]    
	for v in prob.variables():
		if (v.varValue >= 0.000000010):
			items=v.name.split('_')
			if items[0]=='x' and v.varValue >= 0.01:
				xsol.append([int(items[2]),int(items[3]),int(items[1])])
				solution[int(items[2])][int(items[3])]=int(items[1])
				continue
			if items[0]=='p':
				psol.append([int(items[1]),int(items[2]),int(items[3]),v.varValue])
				continue
			if items[0]=='w':
				wsol.append([int(items[1]),int(items[2]),int(items[3]),v.varValue])
				continue
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
	for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k] >=0:
					node_groups[i]=k
					break
	update_district_info()
	return solution,wsol

#no penalty, but with covering reliablity on each demand point
def RFLP2_mip_model(frate,Clevel, rlevel,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	print "Clevel, rlevel",Clevel, rlevel
	xvariables={}
	yvariables={}
	pvariables={}
	wvariables={}
	wcosts={}
	for j in ulist:
		for r in range(Clevel):
			for i in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(r)
				p="p_" +str(i)+"_"+str(j)+"_"+str(r)
				w="w_" +str(i)+"_"+str(j)+"_"+str(r)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
				pvariables[p]=pulp.LpVariable(p, 0, None, pulp.LpContinuous)
				wvariables[w]=pulp.LpVariable(w, 0, None, pulp.LpContinuous)
				wcosts[w]=nodedik[j][i]
	ycosts={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycosts["y_" +str(i)] = facilityCost[i]
	
	obj=""
	for x in yvariables:
		obj+=ycosts[x]*yvariables[x]
	for x in wvariables:
		obj+=wcosts[x]*wvariables[x]
	prob += obj
	
	for j in ulist:
		for r in range(Clevel): 
			s=""
			for i in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
			prob +=s  == 1  

	for j in ulist:
		for r in range(Clevel): 
			for i in centers:
				s=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]-yvariables["y_" +str(i)]
				prob +=s  <= 0  

	for i in centers:
		for j in ulist:
			s=""
			for r in range(Clevel): 
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
			s-=yvariables["y_" +str(i)]
			prob +=s  <= 0

	'''for j in ulist:
		s=xvariables["x_" +str(num_districts)+"_"+str(j)+"_"+str(Clevel)]
		prob +=s  == 1
		'''

	for i in centers:
		for j in ulist:
			s=pvariables["p_" +str(i)+"_"+str(j)+"_0"]
			prob +=s  == 1-frate[i]
			#s-=(1-frate[i])*xvariables["x_" +str(i)+"_"+str(j)+"_0"]
			#prob +=s  == 0
	
	for i in centers:
		for j in ulist:
			for r in range(Clevel): 
				s=wvariables["w_" +str(i)+"_"+str(j)+"_"+str(r)]
				prob +=s  <= pvariables["p_" +str(i)+"_"+str(j)+"_"+str(r)]
				s=wvariables["w_" +str(i)+"_"+str(j)+"_"+str(r)]
				prob +=s  <= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
				s=wvariables["w_" +str(i)+"_"+str(j)+"_"+str(r)]
				s-=pvariables["p_" +str(i)+"_"+str(j)+"_"+str(r)]
				s-=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
				prob +=s >=-1
				
	for i in centers:
		for j in ulist:
			for r in range(1,Clevel): 
				s=pvariables["p_" +str(i)+"_"+str(j)+"_"+str(r)]
				for k in centers: 
					s-=(1-frate[i])*frate[k]/(1-frate[k])*wvariables["w_" +str(k)+"_"+str(j)+"_"+str(r-1)]
				prob +=s ==0
					
	for j in ulist:
		s=""            
		for i in centers:
			for r in range(Clevel): 
				if frate[i]<0.00001:
					s+=-10.0*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
				else: 
					s+=math.log(frate[i])*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(r)]
		prob +=s  <= math.log(rlevel)

	prob.writeLP("_rflp.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	xsol=[]
	psol=[]
	wsol=[]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	solution=[[-1 for x in range(Clevel)]for y in range(num_units) ]    
	solution2=[[0.0 for x in range(Clevel)]for y in range(num_units) ]    

	for v in prob.variables():
		if (v.varValue >= 0.0000010):
			items=v.name.split('_')
			if items[0]=='x':
				solution[int(items[2])][int(items[3])]=int(items[1])
				continue
			if items[0]=='p':
				continue
			if items[0]=='w':
				solution2[int(items[2])][int(items[3])]=v.varValue
				continue
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
	for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k] >=0:
					node_groups[i]=k
					break
	update_district_info()
	
	return solution,solution2

#DR-RUFL(Lu etal.,2015), DR-RCFL (Santiváñez et al.,2018), modified by yfkong 2026.1
# testing by instances
def DR_RUFLP_mip_model(capa,frate,penalty,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	ulist=range(num_units)
	facility=[[x, frate[x]] for x in range(num_districts)]    
	facility.sort(key=lambda x: x[1])
	facility.append([num_districts,1.0])    
	centers=[x[0] for x in facility]    
	p=[0.0 for x in range(num_districts)]
	for k in range(num_districts):
		p[k]=facility[k+1][1]-facility[k][1]
	#print "pissibility test:",p,sum(p),facility[0][1]
	klist=range(num_districts)
	xvariables={}
	zvariables={}
	xcost={}
	for k in klist:
		centers=[facility[x][0] for x in range(k+1)]
		for i in ulist:
			x="z_" +str(i)+"_"+str(k) 
			zvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
				xcost[x]=nodedik[i][j]
	ycost={}
	yvariables={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
	
	obj=""
	for k in klist:
		if p[k]<0.00001:
			continue
		centers=[facility[x][0] for x in range(k+1)]
		for i in ulist:
			x="z_" +str(i)+"_"+str(k)
			obj+=p[k]*penalty*nodes[i][3]*zvariables[x]
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				obj+=p[k]*xcost[x]*xvariables[x]
	for x in yvariables:
		obj+=ycost[x]*yvariables[x]
	prob += obj
	
	for k in klist:
		if p[k]<0.00001:
			continue
		centers=[facility[x][0] for x in range(k+1)]
		for i in ulist:
			s=zvariables["z_" +str(i)+"_"+str(k)]
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
			prob +=s  == 1  
	if capa==0:
		for k in klist:
			if p[k]<0.00001:
				continue
			centers=[facility[x][0] for x in range(k+1)]
			for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)] 
					prob +=s <= yvariables["y_" +str(j)] 
	if capa==1:
		for k in klist:
			if p[k]<0.00001:
				continue
			centers=[facility[x][0] for x in range(k+1)]
			for j in centers:
				s=""
				for i in ulist:
					s+= nodes[i][3]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)] 
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)] 
	prob.writeLP("_rflp.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	virtual=[]
	virtualW=[]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='z':
				virtual.append(nodes[i][3]) #print v.name, v.varValue
				k=int(items[2])
				virtualW.append(p[k]) #print v.name, v.varValue
				continue
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	vdistance=sum(virtual[x]*virtualW[x]*penalty for x in range(len(virtual)))
	print "some locations may be served by virtual facility, total virtual distance:",vdistance
	return 1
	
#Gama robustCFLP and its varients: robustBCFLP, RobustBEECFLP
# tested by instances
def robustCFLP_mip(urange,rlevel,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight
			d=nodedij[i][k]
			if envy_service_objective==1 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
	wvariables={}
	for i in centers:
		wvariables["w_" +str(i)]=pulp.LpVariable("w_" +str(i), 0, None, pulp.LpContinuous)

	zvariables={}
	for k in centers:
		zvariables["z_" +str(k)]=pulp.LpVariable("z_" +str(k), 0, None, pulp.LpContinuous)

	pvariables={}
	for i in ulist:
		for k in centers:
			pvariables["p_" +str(i)+"_"+str(k)]=pulp.LpVariable("p_" +str(i)+"_"+str(k), 0, None, pulp.LpContinuous)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	if max_facility_cost==0 and adaptive_number_of_facilities==1:
		for x in yvariables:
			obj+=ycost[x]*yvariables[x]
	for x in wvariables:
		obj +=bigM * wvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if adaptive_number_of_facilities==0:
		s=""
		for k in centers:
			s+=yvariables["y_"+str(k)]
		prob +=s  == max_num_facility

	if max_facility_cost>0:
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_"+str(k)]
		prob +=s <= max_facility_cost

	'''for k in centers:
		s=""
		for i in ulist:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		s-=num_units*yvariables["y_" + str(k)]
		prob +=s <= 0'''

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0
			
	#zj+pij≥d^ixij,∀i∈I,j∈J
	for k in centers:
		for i in ulist:
			s=zvariables["z_" +str(k)] + pvariables["p_" +str(i)+"_"+str(k)] 
			s-=nodes[i][3]*urange[i]*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s >= 0

	for k in centers:
		for i in ulist:
			s=pvariables["p_" +str(i)+"_"+str(k)] - bigM*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= 0
			
	#∑i∈Idˉixij+zjΓj+∑i∈Ipij≤qjyj,∀j∈J
	#∑i∈Idˉixij+zjΓj+∑i∈Ipij+wi≤qjyj,∀j∈J
	#robust_level=rlevel*num_units/max_num_facility
	robust_level=rlevel
	for k in centers:
		s=""
		for i in ulist:
			s+= pvariables["p_" +str(i)+"_"+str(k)] + nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		s+= robust_level*zvariables["z_" +str(k)] 
		s-= wvariables["w_" +str(k)]
		s-=facilityCapacity[k]*yvariables["y_" +str(k)] 
		prob +=s <= 0

	prob.writeLP("_bsro.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='z':
				print v.name, v.varValue, facilityCapacity[i]
			#if items[0]=='p':
			#	print v.name, v.varValue, nodes[i][3],nodes[i][3]*urange[i]
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k

	update_district_info()
	update_envy_district_info()
	return 1


# Almost robust discrete optimization Baronet et al.(2019)
def Almost_robust_CFLP_mip(K_set,L_set,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
			d=nodedij[i][k]
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	zvariables={}
	for i in centers:
		for k in klist:
			x="z_"+str(i)+"_" +str(k)
			zvariables[x]=pulp.LpVariable(x, 0, None, pulp.LpContinuous)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	for x in yvariables:
		obj+=ycost[x]*yvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0

	for k in klist:
		for i in centers:
			x="z_"+str(i)+"_" +str(k)
			s=zvariables[x] - bigM*yvariables["y_" + str(i)]
			prob +=s <= 0

	for k in klist:
		for i in centers:
			s=""
			for j in ulist:
				s+= K_set[k][j]*xvariables["x_" +str(j)+"_"+str(i)]
			prob +=s <= zvariables["z_"+str(i)+"_" +str(k)]+facilityCapacity[i]*yvariables["y_" +str(i)]

	for i in centers:
		s=""
		for k in klist:
			x="z_"+str(i)+"_" +str(k)
			s+= 1.0/K*zvariables[x]
		prob +=s <= L_set[i]
		
	prob.writeLP("_ardo.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	sum_z=0.0
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			i=int(items[1])
			'''if items[0]=='z':
				sum_z+=v.varValue/K
				print v.name, v.varValue'''
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	#print "sum_z",sum_z
	update_district_info()
	update_envy_district_info()
	return 1

#SUFLP, SCFLP
def Stochastic_CFLP_Kset_mip(K_set,Pk,capa, time_limit,mipgap):
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	obj=""
	for j in centers:
		obj+= facilityCost[j]*yvariables["y_" +str(j)]
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				obj += Pk[k]*K_set[k][i]*nodedij[i][j]*xvariables[x]
	prob += obj

	for k in klist:
		for i in ulist:
			s=""
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
			prob +=s  == 1

	if capa<=1:
		for k in klist:
			for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
					prob +=s <= yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)]
		
	prob.writeLP("_ardo.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	#if capa==1: 
	#	GAP_model(0,time_limit,0.0000001)
			
	update_district_info()
	update_envy_district_info()
	return 1
	
#SUFLP2, SCFLP2
def Stochastic_CFLP2_Kset_mip(K_set,Pk,capa, time_limit,mipgap):
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for i in ulist:
		for j in centers:
			x="x_" +str(i)+"_"+str(j)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	obj=""
	for j in centers:
		obj+= facilityCost[j]*yvariables["y_" +str(j)]
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)
				obj += Pk[k]*K_set[k][i]*nodedij[i][j]*xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s  == 1

	if capa<=1:
		for j in centers:
			for i in ulist:
				s= xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)]
		
	prob.writeLP("_s.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	#if capa==1: 
	#	GAP_model(0,time_limit,0.0000001)
			
	update_district_info()
	update_envy_district_info()
	return 1    
	
	
#different demand-facility pairs for different scenarios
def robust_CFLP_Kset_mip(K_set,capa,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	zvariable= pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	prob += zvariable

	for k in klist:
		for i in ulist:
			s=""
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
			prob +=s  == 1

	if capa<=1:
		for k in klist:
			for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
					prob +=s <= yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)]

	for k in klist:
		s=""
		for j in centers:
			s+= facilityCost[j]*yvariables["y_" +str(j)]
			for i in ulist:
				s+= K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
		prob +=s <= zvariable

		
	prob.writeLP("_ardo.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	if capa==1: 
		GAP_model(0,time_limit,0.0000001)
			
	update_district_info()
	update_envy_district_info()
	return 1


#K_set: facilty status scenarios
def robust_RCFLP_Kset_mip(K_set,capa,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	zvariable= pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	prob += zvariable

	for k in klist:
		for i in ulist:
			s=""
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
			prob +=s  == 1

	if capa<=1:
		for k in klist:
			for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
					prob +=s <= K_set[k][j]*yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= nodes[i][3]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
				prob +=s <= K_set[k][j]*facilityCapacity[j]*yvariables["y_" +str(j)]

	for k in klist:
		s=""
		for j in centers:
			s+= facilityCost[j]*yvariables["y_" +str(j)]
			for i in ulist:
				s+= nodes[i][3]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
		prob +=s <= zvariable
		
	prob.writeLP("_ruflp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	print "cost on all scenarios:",
	for k in klist:
		obj=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for i in ulist:
			for j in NearFacilityList[i]:
				if centersID[j]>=0 and K_set[k][j]==1:
					obj+=nodedik[i][j]
					break
		print int(obj),
	print 

	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	if capa==1: 
		GAP_model(0,time_limit,0.0000001)
			
	update_district_info()
	update_envy_district_info()
	return 1


#K_set: facilty status scenarios
Ksolution=[]
def SP_CFLP_Kset_mip(K_set,Pk,capa,time_limit,mipgap): 
	global centersID
	global node_groups
	global Ksolution
	if len(node_groups)==0: node_groups=[-1 for x in range(num_units)]
	K=len(K_set)
	if len(Ksolution)==0: Ksolution=[[-1 for x in range(num_units)] for k in range(K)]
	gap=mipgap
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	klist=range(K)
	if capa==2 and node_groups[0]>=0: # sub_problem for matheuristic
		ilist=[x for x in range(num_districts) if centersID[x]>=0] 
		ilist2=[x for x in range(num_districts) if centersID[x]<=0] 
		random.shuffle(ilist2)
		n=len(ilist)
		n=min(n,10)
		#n=10
		centers=ilist+ilist2[:n]
	if capa==2 and node_groups[0]<0:
		ilist=[x for x in range(num_districts)] 
		random.shuffle(ilist)
		centers=[]
		supply=0
		demand=max(sum(x) for x in K_set)
		for k in ilist:
			centers.append(k)
			supply+=facilityCapacity[k]
			if supply>1.5*demand:
				break                
		gap=0.05

	xvariables={}
	xcost={}
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
	zvariables={}
	for i in centers:
		for k in klist:
			zvariables["z_" +str(i)+"_"+str(k)]=pulp.LpVariable("z_" +str(i)+"_"+str(k), 0, None, pulp.LpInteger)

	obj=""
	for j in centers:
		obj+= facilityCost[j]*yvariables["y_" +str(j)]
	for k in klist:
		for j in centers:
			obj+=Pk[k]*penalty_on_demand * zvariables["z_" +str(j)+"_"+str(k)]
			for i in ulist:
				obj+= Pk[k]*K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
	prob += obj

	for k in klist:
		for i in ulist:
			s=""
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
			prob +=s  == 1

	for k in klist: #for tight bound
			for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
					prob +=s <= yvariables["y_" +str(j)]
	if capa>=1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)] +zvariables["z_" +str(j)+"_"+str(k)]
				prob += zvariables["z_" +str(j)+"_"+str(k)] <=total_pop*yvariables["y_" +str(j)]
	warmStart=False
	#print "candidate",centers
	if Ksolution[0][0]>=0:	
		for j in centers:
			if centersID[j]<0: continue
			x="y_" +str(j)			
			yvariables[x].setInitialValue(1)      
		for k in klist:
			for i in ulist:
				j=Ksolution[k][i]
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x].setInitialValue(1)
		warmStart=True
		
	prob.writeLP("_ruflp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=warmStart, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=warmStart, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if v.varValue >= 0.010:
			items=v.name.split('_')
			if items[0]=='z':
				print [v,v.varValue],
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				j=int(items[2])
				k=int(items[3])
				Ksolution[k][i]=j
				if k==0: node_groups[i]=j
	'''print "cost on all scenarios:",
	for k in klist:
		obj=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for i in ulist:
			for j in NearFacilityList[i]:
				if centersID[j]>=0 and K_set[k][j]==1:
					obj+=nodedik[i][j]
					break
		print int(obj),
	print 
	if capa==1: 
		GAP_model(0,time_limit,0.0000001)'''
	#print "solution",[x for x in centers if centersID[x]>=0]
	#for x in Ksolution[:2]: print x 
	update_district_info()
	return pulp.value(obj)


def SP_CFLP2_Kset_mip(K_set,Pk,capa,time_limit,mipgap): 
	global centersID
	global node_groups
	if len(node_groups)==0: node_groups=[-1 for x in range(num_units)]
	gap=mipgap
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	if capa==2 and node_groups[0]>=0: # sub_problem for matheuristic
		ilist=[x for x in range(num_districts) if centersID[x]>=0] 
		ilist2=[x for x in range(num_districts) if centersID[x]<=0] 
		random.shuffle(ilist2)
		n=len(ilist)
		n=min(n,10)
		#n=10
		centers=ilist+ilist2[:n]
	if capa==2 and node_groups[0]<0:
		ilist=[x for x in range(num_districts)] 
		random.shuffle(ilist)
		centers=[]
		supply=0
		demand=max(sum(x) for x in K_set)
		for k in ilist:
			centers.append(k)
			supply+=facilityCapacity[k]
			if supply>1.5*demand:
				break                
		gap=0.05
		print centers
	xvariables={}
	xcost={}
	for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
	zvariables={}
	for i in centers:
		for k in klist:
			zvariables["z_" +str(i)+"_"+str(k)]=pulp.LpVariable("z_" +str(i)+"_"+str(k), 0, None, pulp.LpInteger)

	obj=""
	for j in centers:
		obj+= facilityCost[j]*yvariables["y_" +str(j)]
	for k in klist:
		for j in centers:
			obj+=Pk[k]*penalty_on_demand * zvariables["z_" +str(j)+"_"+str(k)]
			for i in ulist:
				obj+= Pk[k]*K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
	prob += obj


	for i in ulist:
			s=""
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)]
			prob +=s  == 1


	for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)]
					prob +=s <= yvariables["y_" +str(j)]
	if capa>=1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)] +zvariables["z_" +str(j)+"_"+str(k)]
	warmStart=False
	if node_groups[0]>=0:	
		initvalues=pmp_mst()
		for x,v in initvalues:
			if x.find("x")==0:  xvariables[x].setInitialValue(v)
			if x.find("y")==0:  yvariables[x].setInitialValue(v)
		warmStart=True

	prob.writeLP("_S.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=warmStart, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=warmStart, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			#if items[0]=='z':
			#	print [v,v.varValue],
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	'''print "cost on all scenarios:",
	for k in klist:
		obj=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for i in ulist:
			for j in NearFacilityList[i]:
				if centersID[j]>=0 and K_set[k][j]==1:
					obj+=nodedik[i][j]
					break
		print int(obj),
	print '''
	'''if capa==1: 
		GAP_model(0,time_limit,0.0000001)'''
			
	update_district_info()
	update_envy_district_info()
	return pulp.value(obj)


#same demand-facility pairs for all scenarios
#capa 0-Rouflp for MIP solver, 1-Rocflp for MIP solver, 2-sub_Rocflp for MH
#optK 0 min-max-cost, zk min-max-regret-zk,z0 min-max-regret-z0
def robust_CFLP2_Kset_mip(K_set,capa,optK,time_limit,mipgap): 
	global centersID
	global node_groups
	global SolSet
	if len(node_groups)==0: node_groups=[-1 for x in range(num_units)]
	gap=mipgap
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	if capa==2 and node_groups[0]>=0: # sub_problem for matheuristic
		ilist=[x for x in range(num_districts) if centersID[x]>=0] 
		ilist2=[x for x in range(num_districts) if centersID[x]<=0] 
		random.shuffle(ilist2)
		n=len(ilist)
		n=min(n,10)
		centers=ilist+ilist2[:n]
	if capa==2 and node_groups[0]<0:
		centers=[]
		demand=[max(K_set[k][x] for k in klist) for x in ulist]
		demand.sort()
		supply=[[x,facilityCapacity[x]] for x in range(num_districts)] 
		supply.sort(key=lambda x:x[1])
		idx=0        
		while 1:
			idx+=1
			if demand[-idx]<supply[idx][1]:
				break
			centers.append(supply[-idx][0])
		print [facilityCapacity[k] for k in centers],demand[-idx:]
		ilist=[x for x in range(num_districts) if x not in centers] 
		random.shuffle(ilist)
		maxsupply=sum(facilityCapacity[k] for k in centers)
		maxdemand=max(sum(x) for x in K_set[:-1])
		for k in ilist:
			centers.append(k)
			maxsupply+=facilityCapacity[k]
			if maxsupply>1.5*maxdemand:
				break                
		gap=0.01    
		#print maxdemand,maxsupply,sum(facilityCapacity[k] for k in centers)#,supply[-idx:],[sum(x) for x in K_set]
		print [facilityCapacity[k] for k in centers[:5]]
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight
			d=nodedij[i][k]
	ycost={}
	yvariables={}
	zvariables={}

	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
	for i in centers:
		for k in klist:
			zvariables["z_" +str(i)+"_"+str(k)]=pulp.LpVariable("z_" +str(i)+"_"+str(k), 0, None, pulp.LpInteger)
	zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	prob += zvariable

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1
	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0
	if capa>=1:
		for k in klist:
			for i in centers:
				s=""
				for j in ulist:
					s+= K_set[k][j]*xvariables["x_" +str(j)+"_"+str(i)]
				prob +=s <= zvariables["z_" +str(i)+"_"+str(k)]+facilityCapacity[i]*yvariables["y_" +str(i)]
				prob += zvariables["z_" +str(i)+"_"+str(k)]<=total_pop*yvariables["y_" +str(i)]
	for k in klist:
		s=""
		for i in centers:
			s+= facilityCost[i]*yvariables["y_" +str(i)]
			for j in ulist:
				s+= K_set[k][j]*nodedij[j][i]*xvariables["x_" +str(j)+"_"+str(i)]
			s+= penalty_on_demand * zvariables["z_" +str(i)+"_"+str(k)]
		prob +=s <= zvariable+optK[k]
	if capa==2 and node_groups[0]>=0: # sub_problem for matheuristic
		ilist=[x for x in range(num_districts) if centersID[x]>=0] 
		random.shuffle(ilist)
		n=int(len(ilist)/2.0+0.6)
		ilist=ilist[:n]
		'''for i in ilist:
			prob += yvariables["y_" +str(i)] == 1'''
	'''if capa==2 and node_groups[0]>=0: # sub_problem for matheuristic
		ilist=[]
		n=int(len(ilist)/2.0+0.6)
		u=random.randint(0,num_units-1)        
		for i in NearFacilityList[u]:
			if centersID[i]<=0: continue
			ilist.append(i)
			if len(ilist)>=n: break       '''
	warmStart=False
	if node_groups[0]>=0:	
		initvalues=pmp_mst()
		for x,v in initvalues:
			if x.find("x")==0:  xvariables[x].setInitialValue(v)
			if x.find("y")==0:  yvariables[x].setInitialValue(v)
		warmStart=True
	#warm start		
	prob.writeLP("_ro.lp")
	#gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		if gap>1:
			solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=warmStart, timeLimit=time_limit, options=['set mip tolerances absmipgap '+ str(gap), 'set parallel -1'])
		else:	solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=warmStart, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		if gap>1:
			solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=warmStart, timeLimit=time_limit,options=[("MIPGapAbs",gap),("TimeLimit",time_limit)])
		else:	solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=warmStart, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved..."
		return 0,0.0
	sub_obj=0.0        
	centersID=[-1 for x in range(num_districts)]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			if v.name=="z": sub_obj=v.varValue
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return sub_obj

#same demand-facility pairs for all scenarios
def robust_CFLP_minreg_mip(K_set,capa,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight
			d=nodedij[i][k]
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	zvariable= pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	prob += zvariable

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0

	if capa==1:
		for k in klist:
			for i in centers:
				s=""
				for j in ulist:
					s+= K_set[k][j]*xvariables["x_" +str(j)+"_"+str(i)]
				prob +=s <= facilityCapacity[i]*yvariables["y_" +str(i)]

	for k in klist:
		obj=UFLP_mip(K_set[k],capa)
		print "scenario",k,"cost",obj
		s=""
		for i in centers:
			s+= facilityCost[i]*yvariables["y_" +str(i)]
			for j in ulist:
				s+= K_set[k][j]*nodedij[j][i]*xvariables["x_" +str(j)+"_"+str(i)]
		prob +=s <= zvariable+obj
		
	prob.writeLP("_ardo.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	update_envy_district_info()
	return 1

# Snyder & Daskin, 2004
def Stochastic_p_robust_CFLP_Kset_mip(K_set,capa,p_robust,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)+"_"+str(k)
				xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
				xcost[x]=K_set[k][i]*nodedij[i][j]/K
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	#zvariable= pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	for x in xvariables:
		obj+=xcost[x]* xvariables[x]
	if fixed_cost_obj==1:
		for x in yvariables:
			obj+=ycost[x]* yvariables[x]
	prob += obj

	for k in klist:
		for i in ulist:
			s=""
			for j in centers:
				s+=xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
			prob +=s  == 1
	if max_num_facility>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob+=s==max_num_facility
	if capa<=1:
		for k in klist:
			for j in centers:
				for i in ulist:
					s= xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
					prob +=s <= yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)]
	k_best_obj=[]
	for k in klist:
		s=""
		kobj=UFLP_mip(K_set[k],capa)
		k_best_obj.append(kobj)        
		print "scenario",k,"cost",kobj,sum(1 for x in centersID if x>=0)
		for j in centers:
			if fixed_cost_obj==1:            
				s+= facilityCost[j]*yvariables["y_" +str(j)]
			for i in ulist:
				s+= K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)+"_"+str(k)]
		prob +=s <= (1+p_robust)*kobj
		
	prob.writeLP("_p_ro.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	'''for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break'''
	update_district_info()
	objvalue=pulp.value(obj)
	robj=[0.0 for x in range(K)]
	if fixed_cost_obj==1:
		robj=[objective_fcost for x in range(K)]
	if capa==0:
		for k in klist:
			for i in ulist:
				for j in NearFacilityList[i]:
					if centersID[j]>=0:
						robj[k]+= K_set[k][i]*nodedij[i][j]
						break
	if capa==1:
		for k in klist:
			dcost=kGAP_mip(K_set[k]) #模型简化带来统计错误
			robj[k]+= dcost
	'''if capa==1:
		for k in klist:
			dcost=sum(nodedij[i][node_groups[i]]*K_set[k][i] for i in ulist)
			robj[k]+= dcost'''
	k_regret=[robj[x]/k_best_obj[x]-1 for x in range(K)]
	return objvalue,robj,k_best_obj,k_regret

# Snyder & Daskin, 2004, simplified for cijk==cij
def Stochastic_p_robust_CFLP2_Kset_mip(K_set,capa,p_robust,time_limit,mipgap): 
	global centersID
	global node_groups
	t=time.time()
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for i in ulist:
		for j in centers:
			x="x_" +str(i)+"_"+str(j)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	obj=""
	if fixed_cost_obj==1:            
		for x in yvariables:
			obj+=ycost[x]* yvariables[x]
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)
				obj+=K_set[k][i]*nodedij[i][j]/K*xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s  == 1
	if max_num_facility>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob+=s==max_num_facility
	if capa<=1:
		for j in centers:
			for i in ulist:
				s= xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)]
	k_best_obj=[]
	for k in klist:
		s=""
		kobj=UFLP_mip(K_set[k],capa)
		k_best_obj.append(kobj)        
		print "scenario",k,"cost",kobj,sum(1 for x in centersID if x>=0)
		for j in centers:
			if fixed_cost_obj==1:
				s+= facilityCost[j]*yvariables["y_" +str(j)]
			for i in ulist:
				s+= K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s <= (1+p_robust)*kobj
	print "modeling time",time.time()-t		
	prob.writeLP("_p_ro.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	'''for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break'''
	update_district_info()
	objvalue=pulp.value(obj)
	robj=[0 for x in range(K)]
	if fixed_cost_obj==1:
		robj=[objective_fcost for x in range(K)]
	if capa==0:
		for k in klist:
			for i in ulist:
				for j in NearFacilityList[i]:
					if centersID[j]>=0:
						robj[k]+= K_set[k][i]*nodedij[i][j]
						break
	'''if capa==1:
		for k in klist:
			dcost=kGAP_mip(K_set[k])
			robj[k]+= dcost'''
	if capa==1:
		for k in klist:
			dcost=sum(nodedij[i][node_groups[i]]*K_set[k][i] for i in ulist)
			robj[k]+= dcost

	k_regret=[robj[x]/k_best_obj[x]-1 for x in range(K)]
	return objvalue,robj,k_best_obj,k_regret


# Snyder & Daskin, 2004, simplified for cijk==cij
def min_p_SCFLP2_Kset_mip(K_set,capa,time_limit,mipgap): 
	global centersID
	global node_groups
	t=time.time()
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for i in ulist:
		for j in centers:
			x="x_" +str(i)+"_"+str(j)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
	pvariable=pulp.LpVariable("p", 0, None, pulp.LpContinuous)
	prob += pvariable

	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s  == 1
	if max_num_facility>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob+=s==max_num_facility
	if capa<=1:
		for j in centers:
			for i in ulist:
				s= xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= yvariables["y_" +str(j)]
	if capa==1:
		for k in klist:
			for j in centers:
				s=""
				for i in ulist:
					s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)]
				prob +=s <= facilityCapacity[j]*yvariables["y_" +str(j)]
	k_best_obj=[]
	for k in klist:
		s=""
		kobj=UFLP_mip(K_set[k],capa)
		k_best_obj.append(kobj)        
		print "scenario",k,"cost",kobj,sum(1 for x in centersID if x>=0)
		for j in centers:
			if fixed_cost_obj==1:
				s+= facilityCost[j]*yvariables["y_" +str(j)]
			for i in ulist:
				s+= K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s <= kobj + pvariable*kobj
	print "modeling time",time.time()-t		
	prob.writeLP("_p_ro.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='p':
				continue
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	'''for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break'''
	update_district_info()
	objvalue=pulp.value(pvariable)
	robj=[0 for x in range(K)]
	if fixed_cost_obj==1:
		robj=[objective_fcost for x in range(K)]
	if capa==0:
		for k in klist:
			for i in ulist:
				for j in NearFacilityList[i]:
					if centersID[j]>=0:
						robj[k]+= K_set[k][i]*nodedij[i][j]
						break
	'''if capa==1:
		for k in klist:
			dcost=kGAP_mip(K_set[k])
			robj[k]+= dcost'''
	if capa==1:
		for k in klist:
			dcost=sum(nodedij[i][node_groups[i]]*K_set[k][i] for i in ulist)
			robj[k]+= dcost
	k_regret=[robj[x]/k_best_obj[x]-1 for x in range(K)]
	update_district_info()
	return objvalue,robj,k_best_obj,k_regret



# new model based on Snyder & Daskin, 2004, simplified for cijk==cij
#sigma_fi+sigma_si+sigma_dij
def Stochastic_p_robust_CFLPinvent_Kset_mip(K_set,p_robust,time_limit,mipgap): 
	global centersID
	global node_groups
	t=time.time()
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	K=len(K_set)
	klist=range(K)
	xvariables={}
	xcost={}
	for i in ulist:
		for j in centers:
			x="x_" +str(i)+"_"+str(j)
			xvariables[x]=pulp.LpVariable(x, 0, 1, pulp.LpBinary)
	yvariables={}
	zvariables={}
	ycost={}
	zcost={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, None, pulp.LpInteger)
		zcost["z_" +str(i)] = facilityCost[i]/facilityCapacity[i]

	obj=""
	for x in yvariables:
		obj+=ycost[x]* yvariables[x]
	for x in zvariables:
		obj+=zcost[x]* zvariables[x]
	for k in klist:
		for i in ulist:
			for j in centers:
				x="x_" +str(i)+"_"+str(j)
				obj+=K_set[k][i]*nodedij[i][j]/K*xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s  == 1
	'''if max_num_facility>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob+=s==max_num_facility'''
	for j in centers:
		for i in ulist:
			s= xvariables["x_" +str(i)+"_"+str(j)]
			prob +=s <= yvariables["y_" +str(j)]
	for k in klist:
		for j in centers:
			#prob += zvariables["z_" +str(j)]<=facilityCapacity[j]
			s=""
			for i in ulist:
				s+= K_set[k][i]*xvariables["x_" +str(i)+"_"+str(j)]
			prob +=s <= zvariables["z_" +str(j)]
	k_best_obj=[]
	for k in klist:
		s=""
		kobj=CFLP_invent_mip(K_set[k])
		k_best_obj.append(kobj)        
		print "scenario",k,"cost",kobj,sum(1 for x in centersID if x>=0)
		for j in centers:
			s += facilityCost[j]*yvariables["y_" +str(j)]
			s += facilityCost[j]/facilityCapacity[j]* zvariables["z_" +str(j)]               
			for i in ulist:
				s+= K_set[k][i]*nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
		prob +=s <= (1+p_robust)*kobj
	print "modeling time",time.time()-t		
	prob.writeLP("_p_ro.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	prob.writeLP("_bsro.lp")

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	zi=[0 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.010):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='z':
				i=int(items[1])
				zi[i]=int(v.varValue+1.0e-7)
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	objvalue=pulp.value(obj)
	robj=[objective_fcost + sum(zi[i]*facilityCost[i]/facilityCapacity[i] for i in centers) for x in range(K)]
	for j in centers:
		if centersID[j]<0: continue
		jlist=[x for x in range(num_units) if node_groups[x]==j]
		for k in range(K):
			dcost=sum(K_set[k][x]*nodedij[x][j] for x in jlist)
			robj[k]+= dcost
		#print robj[k],objective_fcost,sum(zi)*facilityCost[i]/facilityCapacity[i],dcost
	k_regret=[robj[x]/k_best_obj[x]-1 for x in range(K)]
	return objvalue,zi,robj,k_best_obj,k_regret

def CFLP_invent_mip(kset):
	global centersID
	global node_groups
	prob = pulp.LpProblem("_flp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=kset[i]*nodedij[i][k]
	ycost={}
	yvariables={}
	zcost={}
	zvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, None, pulp.LpInteger)
		zcost["z_" +str(i)] = facilityCost[i]/facilityCapacity[i]

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	for x in yvariables:
		obj+=ycost[x]*yvariables[x]
	for x in zvariables:
		obj+=zcost[x]*zvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0

	if max_num_facility>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob+=s==max_num_facility

	for i in centers:
		#prob +=zvariables["z_" +str(i)]<=facilityCapacity[i]
		s=""
		for j in ulist:
			s+= kset[j]*xvariables["x_" +str(j)+"_"+str(i)]
		prob +=s <= zvariables["z_" +str(i)]
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=0, warmStart=True,  options=['set mip tolerances mipgap '+ str(1.0e-10), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=0, options=[("MIPGap",1.0e-10)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	obj=pulp.value(obj)
	return obj
#same demand-facility pairs for all scenarios
def UFLP_mip(kset,capa): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("_flp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=kset[i]*nodedij[i][k]
	ycost={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	if fixed_cost_obj==1:
		for x in yvariables:
			obj+=ycost[x]*yvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	for k in centers:
		for i in ulist:
			s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
			prob +=s <= 0
	if max_num_facility>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob+=s==max_num_facility

	if capa==1:
		for i in centers:
			s=""
			for j in ulist:
				s+= kset[j]*xvariables["x_" +str(j)+"_"+str(i)]
			prob +=s <= facilityCapacity[i]*yvariables["y_" +str(i)]
	
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=0, warmStart=True,  options=['set mip tolerances mipgap '+ str(1.0e-10), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=0, options=[("MIPGap",1.0e-10)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='y':
				i=int(items[1])
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	obj=pulp.value(obj)
	return obj

def kGAP_mip(kset): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("_ap",pulp.LpMinimize)
	centers=[x for x in centersID if x>=0]
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=kset[i]*nodedij[i][k]
	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	for i in centers:
		s=""
		for j in ulist:
			s+= kset[j]*xvariables["x_" +str(j)+"_"+str(i)]
		prob +=s <= facilityCapacity[i]
	
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=0, warmStart=True,  options=['set mip tolerances mipgap '+ str(1.0e-10), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=0, options=[("MIPGap",1.0e-10)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				node_groups[i]=k
	obj=pulp.value(obj)
	return obj

#alpha-reliable beta-service level SCLP
# tested by instances: c196_1
# proposed by yfkong
def reliableSCLP_mip(failrisk,maxR1,rlevel,slevel,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("rflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	yvariables={}
	zvariables={}
	xcost={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
		'''for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight'''
	ycost={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]


	obj=""
	for x in yvariables:
		obj +=ycost[x]*yvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k]>maxR1: continue                        
			s+=yvariables["y_"+str(k)]
		prob +=s - zvariables["z_" +str(i)] >= 0

	s=""
	for i in ulist:
		s += nodes[i][3]*zvariables["z_" +str(i)]
	prob +=s  >= slevel*total_pop

	for i in ulist:
		s=""
		for k in centers:
			d=nodedij[i][k]
			if d>maxR1: continue
			if failrisk[k]<0.00001:
				s+=-10.0*yvariables["y_"+str(k)]
			else: 
				s+=math.log(failrisk[k])*yvariables["y_"+str(k)]
		s+= bigM* zvariables["z_"+str(i)]                   
		if rlevel==0:
			prob +=s  <= bigM-10
		else:                
			prob +=s  <= math.log(rlevel) + bigM

	prob.writeLP("_rlp.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			items=v.name.split('_')
			if items[0]=='z':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1
   
#reliable MCLP  
# proposed by yfkong  
# testing by instances
def reliableMCLP_mip(cap,failrisk,NF,MaxFC, maxR1,maxR2,rlevel,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("rflp",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	yvariables={}
	zvariables={}
	xcost={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
		xcost["z_" +str(i)]=nodes[i][3]
		'''for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			#xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight'''
	ycost={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		ycost["y_" +str(i)] = facilityCost[i]

	obj=""
	for x in zvariables:
		obj +=xcost[x]* zvariables[x]
	prob += obj

	'''for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k]>maxR1: continue                        
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s - zvariables["z_" +str(i)] >= 0'''
	for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k]>maxR1: continue                        
			s+=yvariables["y_" +str(k)]
		prob +=s - zvariables["z_" +str(i)] >= 0


	if NF > 0:
		s=""
		for k in centers:
			s+=yvariables["y_"+str(k)]
		prob +=s  == NF
	
	if MaxFC > 0:
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_"+str(k)]
		prob +=s  <= MaxFC

	#cap==0:            
	'''for k in centers:
		for i in ulist:
			s= xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" +str(k)] 
			prob +=s <= 0'''
	for i in ulist:
		s=""
		for k in centers:
			d=nodedij[i][k]
			if d>maxR2: continue
			if failrisk[k]<0.1e-1:
				s+=-10.0*yvariables["y_"+str(k)]
			else: 
				s+=math.log(failrisk[k])*yvariables["y_"+str(k)]
		s+= bigM* zvariables["z_"+str(i)]                   
		prob +=s  <= math.log(rlevel) + bigM

	'''if cap==1:            
		s=""
		for k in centers:
			s+= (1-failrisk[k])*facilityCapacity[k]*yvariables["y_" +str(k)] 
		for x in zvariables:
			s -=xcost[x]* zvariables[x]
		prob +=s >= 0

		for i in ulist:
			s=""
			for k in centers:
				if nodedij[i][k]>maxR2: continue
				for j in ulist:
					s+=nodes[j][3]*xvariables["x_" +str(j)+"_"+str(k)]
				s-=(1-failrisk[k])*facilityCapacity[k]*yvariables["y_"+str(k)]
			prob +=s  <= 0'''

	prob.writeLP("_rlp.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.10):
			items=v.name.split('_')
			if items[0]=='z':
				continue
			if items[0]=='p':
				print v.name, v.varValue
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	'''if envy_service_objective<10 and spatial_contiguity==0:
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k] >=0:
					node_groups[i]=k
					break'''
	update_district_info()
	return 1

#protected_sclp#
# proposed by yfkong
# testing by instances
def protected_sclp_mip(frate1,frate2, excost, maxR1,slevel, maxR2, rlevel, time_limit,mipgap): 
	#print frate1,frate2, excost, radius1,radius2, rlevel
	global centersID
	global node_groups
	prob = pulp.LpProblem("psclp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	x1variables={}
	x2variables={}
	xcosts={}
	ulist=range(num_units)
	y1variables={}
	y2variables={}
	zvariables={}    
	ycosts={}
	for i in centers:
		y1="y1_" +str(i)
		y2="y2_" +str(i)
		y1variables[y1]=pulp.LpVariable(y1, 0, 1, pulp.LpBinary)
		y2variables[y2]=pulp.LpVariable(y2, 0, 1, pulp.LpBinary)
		ycosts[y1]=facilityCost[i]
		ycosts[y2]=facilityCost[i]+excost[i]
	for i in ulist:
		z="z_" +str(i)
		zvariables[z]=pulp.LpVariable(z, 0, 1, pulp.LpBinary)
	
	obj=""
	for x in y1variables:
		obj += ycosts[x]*y1variables[x]
	for x in y2variables:
		obj += ycosts[x]*y2variables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k]>maxR1: continue                        
			s+=y1variables["y1_" +str(k)]
			s+=y2variables["y2_" +str(k)]
		prob += s-zvariables["z_" +str(i)] >= 0


	s=""
	for i in ulist:
		s+=nodes[i][3]*zvariables["z_" +str(i)]
	prob += s >= slevel*total_pop

	for i in ulist:
			s=""
			for k in centers:
				d=nodedij[i][k]
				if d>maxR2: continue
				if frate1[k]<=0.1e-5:
					s+=-10.0*y1variables["y1_"+str(k)]
				else:
					s+=math.log(frate1[k])*y1variables["y1_"+str(k)]
				if frate2[k]<=0.1e-5:
					s+=-10.0*y2variables["y2_"+str(k)]
				else:
					s+=math.log(frate2[k])*y2variables["y2_"+str(k)]
			s += bigM*zvariables["z_"+str(i)]
			prob +=s  <= bigM + math.log(rlevel)    

	gap=mipgap
	solver=""
	prob.writeLP("_pSCLP.lp")
	
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit),("MIPFocus",1)] )
	solver.setTmpDir()
	solver.actualSolve(prob)
	print "prob.status",prob.status,
	if prob.status<=0:
		#print "model unsolved... or infeasible"
		return 0
	centersID=[-1 for x in range(num_districts)]
	sol1=[-1 for x in range(num_districts)]    
	sol2=[-1 for x in range(num_districts)]    

	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y1': 
				centersID[i]=facilityCandidate[i]
				sol1[i]=i
			if items[0]=='y2':
				centersID[i]=facilityCandidate[i]
				sol2[i]=i

	'''for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k] >=0:
				node_groups[i]=k
				break'''
	print "normal facility", sum(1 for x in sol1 if x>=0),[x for x in sol1 if x>=0]
	print "protected facility",sum(1 for x in sol2 if x>=0),[x for x in sol2 if x>=0]
	#print "facilities",len(sol1)+len(sol2)
	fc=sum(facilityCost[x] for x in sol1 if x>=0)
	fc+=sum(facilityCost[x]+excost[x] for x in sol2 if x>=0)
	print "facility cost", fc

	return 1

#protected_mclp,CMCLP,BMCLP
# proposed by yfkong
# tested by instances
def protected_mclp_mip(frate1,frate2, excost, nf, fcost, maxR1,maxR2, rlevel, time_limit,mipgap): 
	#print frate1,frate2, excost, radius1,radius2, rlevel
	global centersID
	global node_groups
	prob = pulp.LpProblem("psclp",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	x1variables={}
	x2variables={}
	xcosts={}
	ulist=range(num_units)
	y1variables={}
	y2variables={}
	ycosts={}
	zvariables={}
	for i in centers:
		y1="y1_" +str(i)
		y2="y2_" +str(i)
		y1variables[y1]=pulp.LpVariable(y1, 0, 1, pulp.LpBinary)
		y2variables[y2]=pulp.LpVariable(y2, 0, 1, pulp.LpBinary)
		ycosts[y1]=facilityCost[i]
		ycosts[y2]=facilityCost[i]+excost[i]
	for i in ulist:
		zvariables["z_"+str(i)]=pulp.LpVariable("z_"+str(i), 0, 1, pulp.LpBinary)
		
	obj=""
	for i in ulist:
		obj+=nodes[i][3]*zvariables["z_"+str(i)]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k]>maxR1: continue                        
			s+=y1variables["y1_" +str(k)]
			s+=y2variables["y2_" +str(k)]
		prob +=s - zvariables["z_" +str(i)] >= 0
		
	if nf>0:
		s=""
		for k in centers:
			s+=y1variables["y1_"+str(k)]
			s+=y2variables["y2_"+str(k)]
		prob +=s  == nf

	if fcost>0:
		s=""
		for k in centers:
			s+=facilityCost[k]*y1variables["y1_"+str(k)]
			s+=(facilityCost[k]+excost[k])*y2variables["y2_"+str(k)]
		prob +=s <= fcost
  

	for i in ulist:
			s=""
			for k in centers:
				d=nodedij[i][k]
				if d>maxR2: continue
				if frate1[k]<=0.1e-5:
					s+=-10.0*y1variables["y1_"+str(k)]
				else:
					s+=math.log(frate1[k])*y1variables["y1_"+str(k)]
				if frate2[k]<=0.1e-5:
					s+=-10.0*y2variables["y2_"+str(k)]
				else:
					s+=math.log(frate2[k])*y2variables["y2_"+str(k)]
			s+= bigM* zvariables["z_"+str(i)]                   
			prob +=s  <= math.log(rlevel) + bigM

	gap=mipgap
	solver=""
	prob.writeLP("_pSCLP.lp")
	
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit),("MIPFocus",1)] )
	solver.setTmpDir()
	solver.actualSolve(prob)
	#print "prob.status",prob.status,
	if prob.status<=0:
		#print "model unsolved... or infeasible"
		return 0
	centersID=[-1 for x in range(num_districts)]
	sol1=[-1 for x in range(num_districts)]    
	sol2=[-1 for x in range(num_districts)]    

	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y2': 
				centersID[i]=i
				sol2[i]=i
			if items[0]=='y1':
				centersID[i]=i
				sol1[i]=i
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k] >=0:
				node_groups[i]=k
				break

	print "no. facilities",sum(1 for x in sol1 if x>=0)+sum(1 for x in sol2 if x>=0)
	print "normal facility",sum(1 for x in sol1 if x>=0),[x for x in sol1 if x>=0]
	print "protected facility",sum(1 for x in sol2 if x>=0),[x for x in sol2 if x>=0]
	fcost=sum(facilityCost[x] for x in sol1 if x>=0)
	if len(sol2)>0:    
		fcost+=sum(facilityCost[x]+excost[x] for x in sol2 if x>=0)
	print "fcost",fcost    
	update_district_info()
	return 1
	
  
def cpmp_mip_model(num_f,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	weight_of_travelcost=travel_distance_weight
	for i in ulist:
		for k in centers:
			d=nodedij[i][k]
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*weight_of_travelcost
			if d>cflp_max_service_radius:
				xcost["x_" +str(i)+"_"+str(k)]+=nodes[i][3]*penalty_on_demand  
			if location_problem==9: xcost["x_" +str(i)+ "_"+ str(k)]=nodedij[i][k]
			if envy_service_objective==1 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)
	#zvariables={}    
	#for i in ulist:
	#    zvariables[i]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1
	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for k in centers:
		s=""
		for i in ulist:
			s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		if facilityMinimumCapacity>0:
			prob += s >=facilityMinimumCapacity*yvariables["y_" + str(k)]
		s-=facilityCapacity[k]*yvariables["y_" + str(k)]
		prob +=s <= 0

	if cflp_min_service_coverage_percentage >0:
		s=""
		for i in ulist:
			for k in centers:
				if nodedij[i][k]>max_: continue
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  >= total_pop*cflp_min_service_coverage_percentage/100

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0

	for k in centers:
		if k in facility_inclusion_list:
			prob += yvariables["y_" +str(k)] == 1

	prob.writeLP("_cpmpr.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

def CPMP_reduced_model(num_f,model_option,time_limit,mipgap):
	global centersID
	global node_groups
	prob = pulp.LpProblem("cpmp",pulp.LpMinimize)
	ulist=range(num_units)
	centers=range(num_districts)#facilityCandidate
	if num_districts>5*num_f:
		random.shuffle(centers)
		centers=centers[:5*num_f]
	if model_option==2:
		centers=[]
		for k in range(num_districts):
			if centersID[k]<0: continue
			u=nearCustomer[k]
			centers+=NearFacilityList[u][:5]
			centers+=[k]
		centers=list(set(centers))    
	nearFacilitis=copy.deepcopy(NearFacilityList)
	if model_option==2:
		nearFacilitis=[]
		for i in ulist:
			flist=[x for x in NearFacilityList[i] if x in centers]
			nearFacilitis.append(flist)
	#print centers
	xvariables={}
	xcost={}
	nearest_facilities=num_districts*5/num_f
	if model_option==2:
		nearest_facilities=num_districts*10/num_f
	for i in ulist:
		for k in centers:
			if k not in nearFacilitis[i][:nearest_facilities]:
				continue
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]*travel_distance_weight
			d=nodedij[i][k]
			if envy_service_objective==1 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(k)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			if k not in nearFacilitis[i][:nearest_facilities]:
				continue
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for k in centers:
		s=""
		for i in ulist:
			if k not in nearFacilitis[i][:nearest_facilities]:
				continue
			s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		s-=facilityCapacity[k]*yvariables["y_" + str(k)]
		prob +=s <= 0

	if envy_service_objective==1:
		s=""
		for i in ulist:
			for k in centers:
				if k not in nearFacilitis[i][:nearest_facilities]:
					continue
				d=nodedij[i][k]
				if d>envy_service_distance:
					envy=nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
					s+=envy*xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  >= total_pop*envy_service_distance*envy_service_distance*0.25/2

	if model_option==2:
		initvalues=pmp_mst()
		for x,v in initvalues:
			if x.find("x")==0:  xvariables[x].setInitialValue(v)
			if x.find("y")==0:  yvariables[x].setInitialValue(v)
	prob.writeLP("_cpmpr.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True,timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	if prob.status<=0:
		print "model unsolved!..."
		return -1
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

def pmp_mst():
	varibles=[]
	if len(node_groups)<num_units: return varibles
	if node_groups[0]==-1:return varibles
	for i in range(num_units):
		k=node_groups[i]
		if k<0: continue
		v='x_'+str(i)+ '_'+ str(k)
		varibles.append([v,1])
	for i in range(num_districts):
		if centersID[i]<0:continue
		v='y_'+str(i)
		varibles.append([v,1])
	return varibles
def cpmp_var_mip_model(num_f,MADorVar,dmean,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	if MADorVar not in {1,2}: return

	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			d=nodedij[i][k]
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			#xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*(d-dmean)*(d-dmean)
			if MADorVar == 2: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*(d-dmean)*(d-dmean) #minvar
			if MADorVar == 1: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*abs(d-dmean) #minmad
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	#zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	#obj+=1000*zvariable
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	if capacity==0:
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
				prob +=s <= 0
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			s-=facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0
	s=""
	for i in ulist:
		for k in centers:
			s+=nodedik[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
	prob +=s <= dmean*total_pop*(1+mean_distance_epsilon)
	prob +=s >= dmean*total_pop*(1-mean_distance_epsilon)
	#prob +=s <= max_mean_dis*total_pop

	#for k in centers:
	#    i=nearCustomers[k][0]
	#    s = xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
	#    prob += s == 0
	initvalues=pmp_mst()
	for x,v in initvalues:
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	gap=mipgap
	solver=""
	prob.writeLP("_mv.lp")    
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True,timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='z': continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

def cpmp_mean_var_mip_model(num_f,MADorVar,dmean1,dmean2,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	if MADorVar not in {1,2,11,21,12,22}: return -1
	dmean=(dmean1+dmean2)/2
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			d=nodedij[i][k]
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			#xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*(d-dmean)*(d-dmean)
			if MADorVar == 2: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*(d-dmean)*(d-dmean) #minvar
			if MADorVar == 1: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*abs(d-dmean) #minmad
			if MADorVar == 21: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*max(0,d-dmean)*max(0,d-dmean) #minvar+
			if MADorVar == 11: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*max(0,d-dmean) #minmad+
			if MADorVar == 22: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*(d/dmean-1)*(d/dmean-1) #minCV
			if MADorVar == 12: xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*abs(d/dmean-1) #minSI

	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	#zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	#obj+=1000*zvariable
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	if capacity==0:
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
				prob +=s <= 0
		for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM
	if capacity==1:
		'''for i in ulist:
			for k in centers:
				s=""
				for j in centers:
					s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
					s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
					prob +=s  <= bigM'''
		for k in centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			s-=facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0
	s=""
	for i in ulist:
		for k in centers:
			s+=nodedik[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
	prob +=s <= dmean2*total_pop
	prob +=s >= dmean1*total_pop
	#prob +=s <= max_mean_dis*total_pop

	#for k in centers:
	#    i=nearCustomers[k][0]
	#    s = xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
	#    prob += s == 0
	initvalues=pmp_mst()
	for x,v in initvalues:
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	gap=mipgap
	solver=""
	prob.writeLP("_mv.lp")    
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=True,timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return -1
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='z': continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

def pmp_var_quad_mip_model(num_f,time_limit,mipgap): 
	#P-Mean-Variance Location Model
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	for i in ulist:
		for k in centers:
			d=nodedij[i][k]
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	dvariables={}
	for i in ulist:
		dvariables["d_" +str(i)]=pulp.LpVariable("d_" +str(i), 0, None, pulp.LpContinuous)
	dmean=pulp.LpVariable("d", 0, None, pulp.LpContinuous)

	obj=""
	for i in ulist:
		for k in centers:
			d=nodedij[i][k]
			obj+= nodes[i][3] * d* xvariables["x_" +str(i)+"_"+str(k)]

	obj_text=" [ " + str(total_pop)+ " d ^ 2 "
	for i in range(num_units):
		w=str(nodes[i][3])
		w2=str(nodes[i][3]*2)
		obj_text += " + " + w +" d_"+str(i) + " ^ 2 - " + w2 +" d * d_"+str(i)  
	obj_text+= " ] "
	prob += obj
	print "===============Replacing the obj in LP file: _var.lp==========="
	print "=================and solving the LP file: _var.lp ============="
	print obj_text
	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	#nearest assignment
	for i in ulist:
		for k in centers:
			s=""
			for j in centers:
				s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
				s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
				prob +=s  <= bigM

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	#for i in ulist:
	#    for k in centers:
	#        s=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
	#        prob +=s - dvariables["d_" +str(i)]  <= 0
	for i in ulist:
		s=""
		for k in centers:
			s += nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s - dvariables["d_" +str(i)]  == 0

	s=""
	for i in ulist:
		for k in centers:
			s += nodedik[i][k]*xvariables["x_" +str(i)+"_"+str(k)]
	prob += s - total_pop*dmean  == 0
	for k in centers:
		for i in ulist:
			s =xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
			prob +=s <= 0

	for k in centers:
		for i in ulist:
			s =xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
			prob +=s <= 0

	for k in centers:
		for i in ulist:
			s =xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
			prob +=s <= 0
	bm=10000
	for k in centers:
		for i in ulist:
			s = dvariables["d_" +str(i)] + (bm-nodedij[i][k])* yvariables["y_" + str(k)]
			prob +=s <= bm
	
	prob.writeLP("_var.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='d': continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

def cpcp_mip_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	for i in centers:
		x=yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	z=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	obj=100*z
	for x in xvariables:
		obj+= xcost[x]/total_pop*xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	for i in ulist:
		for k in centers:
			s=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] - z
			prob +=s <= 0

	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			s-=facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	if capacity==0:
		for i in ulist:
			for k in centers:
				s=xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
				prob += s <= 0

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0

	#prob.writeLP("_pcp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	maxr=0.0
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=='z': continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
				if maxr<nodedij[i][k]:maxr=nodedij[i][k]
	if capacity==0:
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]>=0: 
					node_groups[i]=k
					break
	update_district_info()
	print "MaxR", maxr
	return 1

def cover_100p_model(num_f,max_radius,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("_mclp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]=nodedik[i][j]/total_pop
			if nodedij[i][j]>max_radius: costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*10000*max_radius
	#zvariables={}
	#for i in ulist:
	#   zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	obj=""
	#for x in zvariables: obj+= zvariables[x]   
	for x in xvariables: obj+= costs[x]*xvariables[x]   
	prob += obj 
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		#s+= zvariables["z_" +str(i)]
		prob += s >=1
	 
	if capacity==0 or capacity==1:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius: continue
				s=xvariables["x_" +str(i)+ "_"+ str(j)] -yvariables["y_" +str(j)]
				prob += s <= 0

	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]>max_radius: continue
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			s-= facilityCapacity[k]*yvariables["y_" +str(k)]
			prob += s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	ws=False
	if len(node_groups)>0:
		ws=True
		for k in range(num_districts):
			if centersID[k]>0:
				yvariables["y_"+str(k)].setInitialValue(1)
			else:
				yvariables["y_"+str(k)].setInitialValue(0)
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]>max_radius: continue
			xvariables["x_" +str(i)+ "_"+ str(k)].setInitialValue(1)

	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=ws, timeLimit=time_limit,options=[("MIPGap",gap),("MIPFocus",1)] )
	solver.setTmpDir()
	solver.actualSolve(prob)
	#if prob.status==2:
	#    return 0
	#print "prob.status",prob.status,
	if prob.status<=0:
		#print "model unsolved... or infeasible"
		return 0
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])

	maxr=max(nodedij[x][node_groups[x]] for x in range(num_units) )
	if maxr<=max_radius: 
		return 1
	else:
		return 0

def mclp_100p_model(num_f,max_radius,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("_mclp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	obj=""
	for x in xvariables:
		obj+= xvariables[x]   
	prob += obj    
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		if len(s)==1: return 0
		prob += s >=1
	 
	if capacity==0:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius: continue
				s=xvariables["x_" +str(i)+ "_"+ str(j)] -yvariables["y_" +str(j)]
				prob += s <= 0

	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]>max_radius: continue
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			if len(s)==1: return 0
			s-= facilityCapacity[k]*yvariables["y_" +str(k)]
			prob += s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	ws=False
	if len(node_groups)>0:
		ws=True
		for k in range(num_districts):
			if centersID[k]>0:
				yvariables["y_"+str(k)].setInitialValue(1)
			else:
				yvariables["y_"+str(k)].setInitialValue(0)
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]>max_radius: continue
			xvariables["x_" +str(i)+ "_"+ str(k)].setInitialValue(1)

	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=ws, timeLimit=time_limit,options=[("MIPGap",gap),("MIPFocus",1)] )
	solver.setTmpDir()
	solver.actualSolve(prob)
	#if prob.status==2:
	#    return 0
	#print "prob.status",prob.status,
	if prob.status<=0:
		#print "model unsolved... or infeasible"
		return 0
	centersID=[-1 for x in range(num_districts)]
	dc=0
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	if prob.status>0: 
		return 1
	else:
		return 0
def mclp_cpcp_model(num_f,max_radius,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("_mclp",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			#if nodedij[i][j]>max_radius: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
	zvariables={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	obj=""
	for i in ulist:
		obj+=zvariables["z_" +str(i)] #nodes[i][3]
	prob += obj

	'''for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1'''
	for i in ulist:
		for k in centers:
			if nodedij[i][k]>max_radius:
				s=xvariables["x_" +str(i)+ "_"+ str(k)]
				prob += s==0
	 
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		s-= zvariables["z_" +str(i)]
		prob += s>=0

	if capacity==0 or capacity==1:
		for i in ulist:
			for j in centers:
				s=xvariables["x_" +str(i)+ "_"+ str(j)] -yvariables["y_" +str(j)]
				prob += s <= 0

	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]>max_radius: continue
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			s-= facilityCapacity[k]*yvariables["y_" +str(k)]
			prob += s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("BestObjStop",num_units),("BestBdStop",num_units-1)] )
	solver.setTmpDir()
	solver.actualSolve(prob)
	#if prob.status==2:
	#    return 0
	print "prob.status",prob.status,
	if prob.status<=0:
		#print "model unsolved... or infeasible"
		return -1
	centersID=[-1 for x in range(num_districts)]
	dc=0
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
			if items[0]=='z':
				dc+=1#nodes[i][3]
	if dc >= num_units: 
		return 1
	else:
		return 0

def sclp_cpcp_model(num_f,capacity,max_radius,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cpcpr",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in yvariables:
		obj += yvariables[x]
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		if len(s)<1: return 0
		prob += s==1
	if capacity==0 or capacity==0:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius: continue
				s=xvariables["x_" +str(i)+ "_"+ str(j)] -yvariables["y_" +str(j)]
				prob += s <= 0
	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]>max_radius: continue
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			s-= facilityCapacity[k]*yvariables["y_" +str(k)]
			prob += s <= 0

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob += s==num_f
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit),("MIPFocus",1)] )
	solver.setTmpDir()
	solver.actualSolve(prob)
	print "prob.status",prob.status,
	if prob.status<=0:
		#print "model unsolved... or infeasible"
		return 0
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_district_info()
	return 1

def cpcp_cpmp_mip_model(num_f,maxr,maxr_ratio,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	sampling=0
	if capacity==1 and num_units>1000 and num_districts>5*num_f:
		sampling=1
		centers=[]
		while len(centers)<3*num_f:
			k=random.randint(0,num_districts-1)
			if k in centers: continue
			centers.append(k)
		#centers=centers[:num_f*3]
		centers+=[x for x in range(num_districts) if centersID[x]>=0]
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			if nodedij[i][k]> maxr: continue
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			r=maxr_ratio
			if r>0.95: r=0.95
			multipler=2.0/(1.0-r)
			if nodedij[i][k]< maxr*r: 
				xcost["x_" +str(i)+"_"+str(k)]=99.5+random.random()
			else:
				d_std=(nodedij[i][k]- maxr*r)/maxr*multipler
				xcost["x_" +str(i)+"_"+str(k)]=100.0+pow(d_std,10)
	yvariables={}
	for i in centers:
		x=yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	
	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k]> maxr: continue
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1
	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == num_f

	if capacity==0:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]> maxr: continue
				s+=xvariables["x_" +str(i)+"_"+str(k)]
			s-=num_units*yvariables["y_" + str(k)]
			prob +=s <= 0
	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]> maxr: continue
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			s-=facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	#prob.writeLP("_pmp.lp")
	initvalues=cflp_mst()
	wstart=False
	if sampling>=0:
		for x,v in initvalues:
			if x.find("x")==0:  
				if x in xvariables:
					xvariables[x].setInitialValue(v)
			if x.find("y")==0:  yvariables[x].setInitialValue(v)
		wstart=True

	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, warmStart=wstart,timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		#solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=wstart,timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=wstart, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)]) #gapAbs=absgap,
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved..."
		return -1,[]
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	r=0.0
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=='z': continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
				if r<nodedij[i][k]:r=nodedij[i][k]
				#print v.name, v.varValue,nodes[i][3]
	update_district_info()
	obj_new=max(nodedij[x][node_groups[x]] for x in range(num_units))
	#print "CPMP",obj_new,r,objective,"|",
	return r,node_groups[:]


#100% cover, minsum+maxstisfaction
def cmclp_biobj_mip_model(min_nf, radius, max_radius,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("cMCLP",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	xvariables={}
	for i in ulist:
		for k in centers:
			if nodedij[i][k] > max_radius: continue
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			
	obj=""
	for i in ulist:
		for k in centers:
			if nodedij[i][k] > max_radius: continue
			if nodedij[i][k] <= radius: 
				obj += (nodes[i][3]*1000000 - nodedik[i][k]) * xvariables["x_" +str(i)+"_"+str(k)]
			else:
				obj -= nodedik[i][k] * xvariables["x_" +str(i)+"_"+str(k)]
	prob += obj
	#cons 2
	for i in ulist:
		s=""
		for k in centers:
			if nodedij[i][k] > max_radius: continue
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob += s == 1

	for k in centers:
		s=""
		for i in ulist:
			if nodedij[i][k] > max_radius: continue
			s+=nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)]
		prob += s <= 0

	s=""
	for j in centers:
		s+=yvariables["y_" + str(j)]
	prob +=s == min_nf

	for k in centers:
		if k in facility_inclusion_list:
			prob += yvariables["y_" +str(k)] == 1

	prob.writeLP("_cmclp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

def mclp_mip_submodel(max_radius,time_limit,mipgap): 
	global centersID
	global node_groups
	u=random.randint(0,num_units-1)
	num_f=sum(1 for x in centersID if x>=0)
	n2=num_f/4
	if n2>20: n2=20
	if n2<8: n2=9
	nf=random.randint(7,n2)
	dlist=[] 
	clist=[] 
	for k in NearFacilityList[u]:
		if centersID[k]>=0: 
			dlist.append(k)
		else:
			clist.append(k)
		if len(dlist)>=nf: break
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	clist+=[x for x in range(num_districts) if centersID[x]<0 and nearCustomer[x] in ulist]
	clist=list(set(clist))
	if len(clist)>4*len(dlist):
		random.shuffle(clist)
		clist=clist[:4*len(dlist)]
	centers=clist+dlist
	for i in range(num_units):
		if node_groups[i]>=0: continue
		for k in centers:
			if nodedij[i][k]<=max_radius:
				ulist.append(i)
				break

	#print len(dlist),len(centers),len(ulist),
	prob = pulp.LpProblem("mclp",pulp.LpMaximize)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	xvariables={}
	for i in ulist:
		for k in centers:
			if nodedij[i][k]> max_radius: continue
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
	zvariables={}
	zcost={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
		zcost["z_" +str(i)]=nodes[i][3]
	obj=""
	for x in zvariables:
		obj +=zcost[x]*zvariables[x]
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		s-= zvariables["z_" +str(i)]
		prob += s>= 0

	for j in centers:
		s=""
		for i in ulist:
			if nodedij[i][j]>max_radius: continue
			s+=nodes[i][3] * xvariables["x_" +str(i)+"_"+str(j)]
		s-= facilityCapacity[j]*yvariables["y_" +str(j)]
		prob += s <= 0

	s=""
	for j in centers:
		s+=yvariables["y_" + str(j)]
	prob +=s == len(dlist)
	"""s=""
	for j in centers:
		s+= facilityCapacity[j]*yvariables["y_" + str(j)]
	prob +=s >= sum(nodes[x][3] for x in ulist)"""
	for k in centers:
		if k in facility_inclusion_list:
			prob += yvariables["y_" +str(k)] == 1

	for k in dlist:
		yvariables["y_" +str(k)].setInitialValue(1)
	for i in ulist:
		k=node_groups[i]
		if k>=0:
			xvariables["x_" +str(i)+"_"+str(k)].setInitialValue(1)

	prob.writeLP("_cmclp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	for x in dlist: centersID[x]=-1
	for x in ulist: node_groups[x]=-1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	return 1

#dual model of CFLP-PS2, too slow to solve capaMCLP with MaxR
def mclp2_mip_submodel(maxr2,max_radius,penalty,time_limit,mipgap): 
	global centersID
	global node_groups
	u=random.randint(0,num_units-1)
	num_f=sum(1 for x in centersID if x>=0)
	n2=num_f/4
	if n2>20: n2=20
	if n2<8: n2=9
	nf=random.randint(7,n2)
	dlist=[] 
	clist=[] 
	for k in NearFacilityList[u]:
		if centersID[k]>=0: 
			dlist.append(k)
		else:
			clist.append(k)
		if len(dlist)>=nf: break
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	clist+=[x for x in range(num_districts) if centersID[x]<0 and nearCustomer[x] in ulist]
	clist=list(set(clist))
	if len(clist)>4*len(dlist):
		random.shuffle(clist)
		clist=clist[:4*len(dlist)]
	centers=clist+dlist
	#print len(dlist),len(centers),len(ulist),
	prob = pulp.LpProblem("mclp",pulp.LpMaximize)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		if objective_overload>0:
			yvariables["w_" +str(i)]=pulp.LpVariable("w_" +str(i), 0, None, pulp.LpInteger)
	xvariables={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
	zvariables={}
	zcost={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
		zcost["z_" +str(i)]=nodes[i][3]

	obj=""
	for x in zvariables:
		obj +=zcost[x]*zvariables[x]
	if objective_overload>0:
		for i in centers:
			obj-=penalty*yvariables["w_" +str(i)]
	for i in ulist:
		for k in centers:
			if nodedij[i][k]< maxr2: continue
			obj-= penalty*nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob += s == 1

	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		s-= zvariables["z_" +str(i)]
		prob += s == 0

	for j in centers:
		s=""
		for i in ulist:
			s+=nodes[i][3] * xvariables["x_" +str(i)+"_"+str(j)]
		if objective_overload>0:
			s+= -yvariables["w_" +str(j)]
		s+= -facilityCapacity[j]*yvariables["y_" +str(j)]
		prob += s <= 0
	if objective_overload>0:
		for j in centers:
			s= yvariables["w_" +str(j)]-100000*yvariables["y_" +str(j)]
			prob += s <= 0
	for k in centers:
		if k in facility_inclusion_list:
			prob += yvariables["y_" +str(k)] == 1

	s=""
	for j in centers:
		s+=yvariables["y_" + str(j)]
	prob +=s == len(dlist)
	"""s=""
	for j in centers:
		s+= facilityCapacity[j]*yvariables["y_" + str(j)]
	prob +=s >= sum(nodes[x][3] for x in ulist)"""

	for k in dlist:
		yvariables["y_" +str(k)].setInitialValue(1)
	for i in ulist:
		k=node_groups[i]
		if k>=0:
			xvariables["x_" +str(i)+"_"+str(k)].setInitialValue(1)

	prob.writeLP("_sub_mclp2.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit,warmStart=True, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,warmStart=True,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved..."
		return []
	for x in dlist: centersID[x]=-1
	for x in ulist: node_groups[x]=-1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	return 1


def mclp_add_evaluate(maxr):
	clist=[x for x in range(num_districts) if centersID[x]<0]
	random.shuffle(clist)
	assignlist=[]
	maxtry=min(10,len(clist))
	for idx in range(maxtry):
		k=clist[idx]
		alist=[]
		supply=facilityCapacity[k]
		for i in nearCustomers[k]:
			if node_groups[i]>=0: continue
			if nodedij[i][k]>maxr: break
			if nodes[i][3]>supply: break
			alist.append(i)
			supply-=nodes[i][3]
		assignlist.append([facilityCapacity[k]-supply,k,alist[:]])
	assignlist.sort(key=lambda x:-x[0])
	return assignlist[0][1],assignlist[0][2]
def assign_MCLP(maxr):
	global node_groups
	ulist = [x for x in range(num_units) if node_groups[x]==-1]
	random.shuffle(ulist)
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if nodedij[i][k]>maxr: break
			if nodes[i][3]<=facilityCapacity[k]-district_info[k][1]:
				node_groups[i]=k
				update_district_info()
				break
def assign_MCLP2(maxr):
	global node_groups
	ulist = [x for x in range(num_units) if nodedij[x][node_groups[x]]>maxr]
	random.shuffle(ulist)
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if nodedij[i][k]>maxr: break
			if nodes[i][3]<=facilityCapacity[k]-district_info[k][1]:
				node_groups[i]=k
				update_district_info()
				break

def pcp_matheuristic(num_f, maxr,capacity, pop_size, max_loops):
	global node_groups
	global centersID
	global all_solutions
	global region_pool
	global pool_index
	global max_num_facility
	max_num_facility=num_f
	region_pool=[]
	pool_index=[[] for x in range(num_districts)]
	t=time.time()
	for idx in range(pop_size):
		r2=maxr*(95+random.random())/100.0
		cpcp_bs(num_f,capacity,0.0,r2,0.05)
		update_district_info()
		maxd=10000*objective_overload+max(nodedij[x][node_groups[x]] for x in range(num_units))*100+objective/total_pop
		all_solutions.append([maxd,centersID[:],node_groups[:]])
		print "init solution, minmax:", maxd, objective_overload, int(time.time()-t)
	not_improved=0
	loops=0
	all_solutions.sort(key=lambda x :x[0])
	bast_obj=all_solutions[0][0]
	while 1:
		r=random.random()
		idx=int(pow(r,1.6)*min(pop_size,len(all_solutions))*0.9999)
		centersID=all_solutions[idx][1][:]
		node_groups=all_solutions[idx][2][:]
		maxd_old=all_solutions[idx][0]
		update_district_info()
		cpcp_sub_model(num_f,capacity,3600,0.000001)
		update_district_info()
		update_region_pool_all()
		maxd=10000*objective_overload+max(nodedij[x][node_groups[x]] for x in range(num_units))*100+objective/total_pop
		all_solutions.append([maxd,centersID[:],node_groups[:]])
		all_solutions.sort(key=lambda x:x[0])
		all_solutions=pop_selection(all_solutions)

		not_improved+=1
		if maxd<bast_obj:
			not_improved-= int( (bast_obj-maxd)*10000*max_loops/maxd +0.5)
			bast_obj=maxd
			if not_improved<0: not_improved=0
		loops+=1
		print "loop:", loops, "best:", bast_obj, "current:", maxd_old,"->",maxd,"Info:", objective_overload,not_improved, int(time.time()-t)
		if not_improved>=max_loops: break
	centersID=all_solutions[0][1][:]
	node_groups=all_solutions[0][2][:]
	#pcp_scp_model(100,0.00000001)   
	update_district_info()
	print "obj", max(nodedij[x][node_groups[x]] for x in range(num_units))

def cpcp_sub_model(num_f,capacity,time_limit,mipgap): 
	global centersID
	global node_groups
	#select a region     
	n=random.randint(min(7,num_f/2),min(30,num_f))    
	u=random.randint(0,num_units-1)
	if objective_overload>0 and random.random()>0:
		rlist=[k for k in range(num_districts) if district_info[k][4]>0]
		random.shuffle(rlist)
		r=rlist[0]
		u=nearCustomer[r]
	else:           
		rlist=[ [x,nodedij[x][node_groups[x]]] for x in range(num_units)]
		rlist.sort(key=lambda x: -x[1])
		rlist=[ rlist[x][0] for x in range(num_units/10)]
		random.shuffle(rlist)
		u=rlist[0]
	dlist=[]
	for k in NearFacilityList[u]:
		if centersID[k]<0: continue
		dlist.append(k)
		if len(dlist)==n: break
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]    
	#select candadates
	clist=[NearFacilityList[x][0] for x in ulist ]
	clist=[x for x in clist if centersID[x]<0]
	random.shuffle(clist)
	cnum=8000/len(ulist)-n
	if cnum<n:cnum=n
	if cnum>3*n:cnum=3*n
	centers=list(set(clist[:cnum] + dlist))
	existing_centers=[]
	if objective_overload==0:
		existing_centers=[x for x in range(num_districts) if centersID[x]>=0 and x not in dlist and facilityCapacity[x]>district_info[x][1]]
		maxd=max(nodedij[x][node_groups[x]] for x in ulist) #range (num_units)
		existing_centers=[x for x in existing_centers if min(nodedij[y][x] for y in ulist)<maxd]
	#print dlist,existing_centers,centers,
	print [len(dlist),len(existing_centers),len(centers),len(ulist)],
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	#centers=range(num_districts)#facilityCandidate
	#ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
		for k in existing_centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			xcost["x_" +str(i)+"_"+str(k)]=nodedik[i][k]
	yvariables={}
	zvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		if capacity==1:    
			zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, None, pulp.LpInteger)
	z=pulp.LpVariable("z", 0, None, pulp.LpContinuous)

	obj=100*z
	if capacity==1:    
		for x in zvariables:
			obj+= 1000000*zvariables[x]
	for x in xvariables:
		obj+= xcost[x]/total_pop*xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers+existing_centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	s=""
	for k in centers:
		s+=yvariables["y_"+str(k)]
	prob +=s  == len(dlist)

	for i in ulist:
		for k in centers+existing_centers:
			s=nodedij[i][k]*xvariables["x_" +str(i)+"_"+str(k)] - z
			if nodedij[i][k]>0: prob +=s <= 0

	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= zvariables["z_" + str(k)]+facilityCapacity[k]*yvariables["y_" + str(k)]
		for k in existing_centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= facilityCapacity[k]-district_info[k][1]
	if capacity==0:
		for i in ulist:
			for k in centers:
				s=xvariables["x_" +str(i)+"_"+str(k)] - yvariables["y_" + str(k)]
				prob += s <= 0
	'''for i in ulist:
		for k in centers:
			v=0
			if node_groups[i]==k: v=1
			xvariables["x_" +str(i)+"_"+str(k)].setInitialValue(v)
		v=0
		if k in node_groups: v=1
		yvariables["y_"+str(k)].setInitialValue(v)'''
	maxd1=100000*objective_overload+max(nodedij[x][node_groups[x]] for x in ulist)
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	if prob.status<=0:
		print "prob.status",prob.status,
		prob.writeLP("_subpcp.lp")  
		exit()        
		return 0
	for k in dlist: centersID[k]=-1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if len(items)<2:
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	if capacity==0:
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]>=0: 
					node_groups[i]=k
					break
	update_district_info()
	maxd2=100000*objective_overload+max(nodedij[x][node_groups[x]] for x in ulist)
	print [int(maxd1*100)/100.0,"->",int(maxd2*100)/100.0],
	return 1

def pcp_scp_model(maxtime,mipgap):
	global node_groups
	global centersID
	if len(region_pool)<=10:
		print "len(region_pool)<=10", len(region_pool)
		return 0
	prob = pulp.LpProblem("_spp",pulp.LpMinimize)
	variables=[]
	costs=[]
	print "set covering ...",len(region_pool),
	r=pulp.LpVariable("r", 0, None,pulp.LpContinuous)
	for i in range(len(region_pool)):
		x=pulp.LpVariable("x_" +"{0:07d}".format(i), 0, 1,pulp.LpBinary)
		variables.append(x)
		k=region_pool[i][4]
		ulist=region_pool[i][0]
		cost=max(nodedij[x][k] for x in ulist)
		costs.append(cost)
	prob+=r

	for i in range(len(region_pool)):
		s=costs[i]*variables[i]
		prob += s<=r

	rlist=[[] for i in range(num_units)]
	for j in range(len(region_pool)):
		for x in region_pool[j][0]:
			rlist[x].append(j)
	for i in range(num_units):
		s=""
		for x in rlist[i]:
			s+=variables[x]
		prob+=s >= 1
 
	for k in range(num_districts):
		s=""
		for i in range(len(region_pool)):
			if region_pool[i][4]!=k: continue
			s+=variables[i]
		if len(s)>0: prob+=s <= 1

	s=""
	for i in range(len(variables)):
		s+=variables[i]
	prob+= s==max_num_facility

	prob.writeLP("_spp.lp")
	vars=spp_mst()
	for x,v in vars: variables[x].setInitialValue(v)
	solver=0
	if mip_solver=='cbc': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.COIN_CMD(timeLimit=maxtime,mip=1,msg=solver_message,gapRel=mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,warmStart=True,timeLimit=maxtime,options=['set parallel -1','set mip tolerances mipgap ' + str(mipgap)])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	#if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
	print "... prob.status:", prob.status
	if prob.status<=0:
	   print "prob.status<0..."
	   return prob.status #failer
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	for v in prob.variables():
		if (v.varValue >= 0.99):
			items=v.name.split('_')
			if len(items)<2: continue
			i=int(items[1])
			k=region_pool[i][4]
			#print k,costs[i],facilityCost[k]
			centersID[k]=facilityCandidate[k]
			for x in region_pool[i][0]:
				node_groups[x]=k
	update_district_info()
	return 1 #success


def mclp_matheuristic(num_f, maxr, pop_size, max_loops):
	global node_groups
	global centersID
	global all_solutions
	maxcovered=0
	t=time.time()
	for idx in range(pop_size):
		node_groups=[-1 for x in range(num_units)]
		#clist=range(num_districts)
		#random.shuffle(clist)
		centersID=[-1 for x in range(num_districts)]
		while 1:
			nf = sum(1 for x in centersID if x>=0)
			if nf>=num_f: break
			k,ulist=mclp_add_evaluate(maxr)
			centersID[k]=facilityCandidate[k]
			for x in ulist:
				node_groups[x]=k
		covered=sum(nodes[x][3] for x in range(num_units) if node_groups[x]>=0)
		if covered>maxcovered: maxcovered=covered
		all_solutions.append([-covered,centersID[:],node_groups[:]])
		update_district_info()
		print objective_overload,
		print "init solution, demand covered:", covered, int(time.time()-t)
	not_improved=0
	loops=0
	while 1:
		r=random.random()
		idx=int(r*r*pop_size)
		centersID=all_solutions[idx][1][:]
		node_groups=all_solutions[idx][2][:]
		covered_old=-all_solutions[idx][0]
		update_district_info()
		mclp_mip_submodel(maxr2,maxr, 3, 0.0001)
		update_district_info()
		assign_MCLP(maxr)
		covered=sum(nodes[x][3] for x in range(num_units) if node_groups[x]>=0)
		for i in range(num_units):
			k=node_groups[i]
			if k<0: continue
			if nodedij[i][k]>=maxr: print i,
		issame=0
		all_solutions.append([-covered,centersID[:],node_groups[:]])
		all_solutions.sort(key=lambda x:x[0])
		all_solutions=pop_selection(all_solutions)

		not_improved+=1
		if covered>maxcovered:
			not_improved-= (covered-maxcovered)*10000*max_loops/maxcovered
			if not_improved<0: not_improved=0
			maxcovered=covered
		loops+=1
		print "loop:", loops, "best:", maxcovered, int(maxcovered*10000/total_pop)/100.0, "current:", covered_old,"->",covered,"Info:", not_improved, int(time.time()-t)
		if not_improved>=max_loops: break
	centersID=all_solutions[0][1][:]
	node_groups=all_solutions[0][2][:]
	update_district_info()
	print maxcovered, maxcovered/total_pop,all_solutions[0][0]

def mclp2_matheuristic(num_f, maxr2,maxr, pop_size, max_loops):
	global node_groups
	global centersID
	global all_solutions
	maxcovered=-MAXNUMBER
	t=time.time()
	for idx in range(pop_size):
		node_groups=[-1 for x in range(num_units)]
		#clist=range(num_districts)
		#random.shuffle(clist)
		centersID=[-1 for x in range(num_districts)]
		while 1:
			nf = sum(1 for x in centersID if x>=0)
			if nf>=num_f: break
			k,ulist=mclp_add_evaluate(maxr)
			centersID[k]=facilityCandidate[k]
			#print k,ulist
			for x in ulist:
				node_groups[x]=k
		ulist=[x for x in range(num_units) if node_groups[x]<0]
		for i in ulist: 
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				node_groups[i]=k
				break
		update_district_info()
		#print objective,objective_overload,node_groups[:100]
		covered=0
		not_covered=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]>maxr2: not_covered+=nodes[x][3]
			if nodedij[i][k]<=maxr: covered+=nodes[x][3]
		covered-=not_covered*100+objective_overload*100
		if covered>maxcovered: maxcovered=covered
		all_solutions.append([-covered,centersID[:],node_groups[:]])
		
		print "init solution, demand covered:", covered, objective_overload,not_covered,int(time.time()-t)
	not_improved=0
	loops=0
	penalty=100.0
	while 1:
		r=random.random()
		idx=int(r*r*pop_size)
		centersID=all_solutions[idx][1][:]
		node_groups=all_solutions[idx][2][:]
		covered_old=-all_solutions[idx][0]
		update_district_info()
		
		mclp2_mip_submodel(maxr2, maxr,penalty,20,0.01)
		update_district_info()
		assign_MCLP2(maxr2)
		assign_MCLP2(maxr)
		covered=0
		not_covered=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]>maxr2: not_covered+=nodes[x][3]
			if nodedij[i][k]<=maxr: covered+=nodes[x][3]
		print covered,not_covered,objective_overload,
		covered-=not_covered*100+objective_overload*100
		if not_covered+objective_overload<covered/10: penalty=1000
		if not_covered+objective_overload<covered/100: penalty=100000
		
		#print covered
		all_solutions.append([-covered,centersID[:],node_groups[:]])
		all_solutions.sort(key=lambda x:x[0])
		all_solutions=pop_selection(all_solutions)

		not_improved+=1
		if covered>maxcovered:
			not_improved=0 #-= (covered-maxcovered)*10000*max_loops/maxcovered
			if not_improved<0: not_improved=0
			maxcovered=covered
		loops+=1
		print "loop:", loops, "best:", maxcovered, int(maxcovered*10000/total_pop)/100.0, "current:", covered_old,"->",covered,"Info:", not_improved, int(time.time()-t)
		if not_improved>=max_loops: break
	centersID=all_solutions[0][1][:]
	node_groups=all_solutions[0][2][:]
	update_district_info()
	print maxcovered, maxcovered/total_pop,all_solutions[0][0]

def partial_GAP_model(time_limit): #GAP 
	global node_groups
	update_district_info()
	prob = pulp.LpProblem("_sap",pulp.LpMinimize)
	variables={}
	costs={}
	ulist=[x for x in range(num_units) if node_groups[x]<0]
	print "len(ulist)",len(ulist),sum(nodes[x][3] for x in ulist),sum(nodes[x][3] for x in range(num_units) if node_groups[x]>=0)
	centers=[x for x in range(num_districts) if centersID[x]>=0]
	for i in ulist:
		for j in centers:
			variables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]=nodedik[i][j]
	obj=""
	for x in variables:
		obj += costs[x]*variables[x]
	prob +=obj
	for i in ulist:
		s=""
		for j in centers:
			s+=variables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1

	for k in centers:
		s=""
		for i in ulist:
			s+=nodes[i][3]*variables["x_" +str(i)+ "_"+ str(k)]
		prob+=s <= facilityCapacity[k]-district_info[k][1] #
	prob.writeLP("_gap.lp")
	#time_limit=500
	mipgap=0.005
	solver=pulp.apis.COIN_CMD(mip=1,msg=0,gapRel = mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	#prob.solve(solver=cbc)
	if mip_solver=="cplex":
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap 0.005'])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,timeLimit=time_limit,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	#arcpy_print("solver status: " + pulp.LpStatus[prob.status])
	if prob.status<=0:
		print "model unsolved..."
		return prob.status
	for v in prob.variables():
		if (v.varValue >= 0.90):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			k=int(items[2])
			node_groups[i]=k
	update_district_info()
	return prob.status

def capa_mclp_mip_model3(min_nf,max_radius,time_limit,mipgap): #100% covered
	global centersID
	global node_groups
	#lb=lscp_lp_model(max_radius,cover_pecentage,time_limit,mipgap)
	#min_nf=int(lb+0.999)
	prob = pulp.LpProblem("pcp",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	xvariables={}
	for i in ulist:
		for k in centers:
			#if nodedij[i][k]> max_radius: continue
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			
	obj=""
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius: 
				obj+=nodedik[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
			else:
				obj+=(nodedik[i][j]+1000*nodes[i][3])*xvariables["x_" +str(i)+"_"+str(j)]
	prob += obj

	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		prob += s == 1

	for j in centers:
		s=""
		for i in ulist:
			s+=nodes[i][3] * xvariables["x_" +str(i)+"_"+str(j)]
		s-= facilityCapacity[j]*yvariables["y_" +str(j)]
		prob += s <= 0

	s=""
	for j in centers:
		s+=yvariables["y_" + str(j)]
	prob +=s == min_nf

	prob.writeLP("_cmclp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
								
				node_groups[i]=k
					 
	update_district_info()
	return 1

def capa_mclp_mip_model2(min_nf,max_radius,time_limit,mipgap): #100% covered
	global centersID
	global node_groups
	#lb=lscp_lp_model(max_radius,cover_pecentage,time_limit,mipgap)
	#min_nf=int(lb+0.999)
	prob = pulp.LpProblem("pcp",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	xvariables={}
	for i in ulist:
		for k in centers:
			#if nodedij[i][k]> max_radius: continue
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			
	zvariables={}
	zcost={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
		zcost["z_" +str(i)]=nodes[i][3]
	obj=""
	for x in zvariables:
		obj +=zcost[x]*zvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for j in centers:
			#if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		#s-= zvariables["z_" +str(i)]
		prob += s == 1

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+"_"+str(j)]
		s-= zvariables["z_" +str(i)]
		prob += s >= 0

	for j in centers:
		s=""
		for i in ulist:
			#if nodedij[i][j]>max_radius: continue
			s+=nodes[i][3] * xvariables["x_" +str(i)+"_"+str(j)]
		s-= facilityCapacity[j]*yvariables["y_" +str(j)]
		prob += s <= 0

	s=""
	for j in centers:
		s+=yvariables["y_" + str(j)]
	prob +=s == min_nf

	prob.writeLP("_cmclp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	update_district_info()
	return 1

#maximum covering location  
def mclp_mip_model(min_nf,max_radius,time_limit,mipgap): 
	global centersID
	global node_groups
	#lb=lscp_lp_model(max_radius,cover_pecentage,time_limit,mipgap)
	#min_nf=int(lb+0.999)
	prob = pulp.LpProblem("pcp",pulp.LpMaximize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	zvariables={}
	zcost={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
		zcost["z_" +str(i)]=nodes[i][3]
	obj=""
	for x in zvariables:
		obj +=zcost[x]*zvariables[x]
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=yvariables["y_" + str(j)]
		s-= zvariables["z_" +str(i)]
		prob += s>= 0

	s=""
	for j in centers:
		s+=yvariables["y_" + str(j)]
	prob +=s == min_nf

	#prob.writeLP("_mclp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k] >=0:
				node_groups[i]=k
				break
	update_district_info()
	return 1

def lscp_mip_model_init(max_radius,cover_pecentage,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	random.shuffle(centers)
	#centers=centers[:num_districts*9/10]
	ulist=range(num_units)
	xvariables={}
	costs={}
	yvariables={}
	
	for i in centers:
		dis=0.0
		for j in nearCustomers[i]:
			if nodedij[j][i]>max_radius:
				break
			dis+=nodedik[j][i]
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i] + dis*(9.5+random.random())/10
	zvariables={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpInteger)
	
	obj=""
	for x in yvariables:
		obj +=costs[x]*yvariables[x]
	prob += obj

	for k in centers:
		if k in facility_inclusion_list:
			prob += yvariables["y_" +str(k)] == 1

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=yvariables["y_" + str(j)]
		prob +=s - zvariables["z_" +str(i)] >= 0

#    for i in ulist:
#        for j in centers:
#            if nodedij[i][j]>max_radius: continue
#            s=yvariables["y_" + str(j)]+ zvariables["z_" +str(i)]
#            prob +=s <= 1

	s=""
	for i in ulist:
		s+=nodes[i][3]*zvariables["z_" +str(i)]
	prob += s>=total_pop*cover_pecentage/100
	#maxuc=total_pop-total_pop*cover_pecentage/100
	#prob += s<=maxuc
	prob.writeLP("_lscp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved..."
		return 0
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k] >=0:
				node_groups[i]=k
				break
	update_district_info()
	return 1

def lscp_mip_model_init2(maxr2,maxr,cover_pecentage,time_limit,mipgap): 
	global centersID
	global node_groups
	global district_info
	prob = pulp.LpProblem("_clscp",pulp.LpMinimize)
	centers=range(num_districts)
	random.shuffle(centers)
	#centers=centers[:num_districts*9/10]
	centers=list(set(centers+facility_inclusion_list))
	ulist=range(num_units)
	yvariables={}
   
	costs={}
	for i in centers:
		dis=0.0
		for j in nearCustomers[i]:
			if nodedij[j][i]>maxr2:
				break
			dis+=nodedik[j][i]
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i] + dis*(19.5+random.random())/20

	zvariables={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpInteger)
	obj=""
	for x in yvariables:
		obj += costs[x]*yvariables[x]
	prob += obj

	for k in centers:
		if k in facility_inclusion_list:
			prob += yvariables["y_" +str(k)] == 1

	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>maxr: continue
			s+=yvariables["y_" + str(j)]
		s -= zvariables["z_" +str(i)]
		prob += s>= 0

	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>maxr2: continue
			s+=yvariables["y_" + str(j)]
		prob += s >= 1

	s=""
	for i in ulist:
		s+=nodes[i][3]*zvariables["z_" +str(i)]
	prob += s>=total_pop*cover_pecentage/100.0
	
	prob.writeLP("_sclp_init3.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	if prob.status<=0:
		print "model unsolved..."
		return 0
	centersID=[-1 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			break
	return 1   
 
def clscp_mip_model_init(maxr2,maxr,cover_pecentage,time_limit,mipgap): 
	global centersID
	global node_groups
	global district_info
	prob = pulp.LpProblem("_clscp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	sampling=0
	if total_supply>=20*total_pop:
		sampling=1
		min_nf=int(total_pop*num_districts/total_supply)
		#centers=k_medoids_cflpr_sampling(min_nf*10)
		clist=range(num_districts)
		random.shuffle(clist)
		clist=clist[:min_nf*20]
		centers=list(set(clist+facility_inclusion_list))
	covered_units=[[] for x in range(num_districts)]
	covered_cost=[facilityCost[x]*fixed_cost_obj for x in range(num_districts)]
	for k in range(num_districts):
		covered=[]
		if k not in centers: continue
		supply=facilityCapacity[k]*1.15
		cost=fixed_cost_obj*facilityCost[k]
		for i in nearCustomers[k]:
			if supply<nodes[i][3]: continue
			if nodedij[i][k]>maxr2: continue
			supply-=nodes[i][3]
			covered.append(i)
			cost+=nodedik[i][k]#*envy_objective_weight_of_travelcost
			if nodedij[i][k]>maxr2:
				cost+=nodes[i][3]*penalty_on_demand
			'''if envy_service_objective==1 and nodedij[i][k]>envy_service_distance:
				cost+=nodes[i][3]*envy_objective_weight*(nodedij[i][k]-envy_service_distance)*(nodedij[i][k]-envy_service_distance)*(9.5+random.random())/10
			if envy_service_objective==4 and nodedij[i][k]>envy_service_distance:
				cost+=nodes[i][3]*envy_objective_weight*(nodedij[i][k]-envy_service_distance)*(9.5+random.random())/10'''
		covered_units[k]=covered[:]
		covered_cost[k]+=cost
		if sampling==0:
			covered_cost[k]*=(9.5+random.random())/10
	avg_covered_cost=sum(covered_cost)/num_districts
	ulist=range(num_units)
	yvariables={}
	#for k in range(num_districts):
	#    print k, facilityCapacity[k],len(covered_units[k])
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	zvariables={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary) #covered?
	for i in ulist:
		zvariables["z2_" +str(i)]=pulp.LpVariable("z2_" +str(i), 0, 1, pulp.LpBinary) #maxr covered

	zvariable=pulp.LpVariable("z", 0, None, pulp.LpInteger)
	obj=""
	for k in centers:
		obj += covered_cost[k]*yvariables["y_" +str(k)] 
	for i in ulist:
		obj += nodes[i][3]*penalty_on_demand*zvariables["z_" +str(i)]
	obj += penalty_on_demand * zvariable
	prob += obj
	'''
	s=""
	for k in centers:
		s+=facilityCapacity[k]*yvariables["y_" +str(k)]
	prob +=s >= total_pop'''

	#for k in centers:
	#    if k in facility_inclusion_list:
	#        prob += yvariables["y_" +str(k)] == 1

	if adaptive_number_of_facilities==0:
		s=""
		for k in centers:
			s+=yvariables["y_" +str(k)]
		prob +=s == max_num_facility

	if max_facility_cost>0:
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		prob += s <= max_facility_cost

	for i in ulist:
		s=""
		for j in centers:
			if i in covered_units[j]: 
				s+=yvariables["y_" + str(j)]
		s += zvariables["z_" +str(i)]
		prob += s>= 1

	for i in ulist:
		s=""
		for j in centers:
			if i in covered_units[j]: 
				if nodedij[i][j]<=maxr: 
					s+=yvariables["y_" + str(j)]
		s -= zvariables["z2_" +str(i)]
		prob += s>= 0
	if cover_pecentage>0:
		s=""
		for i in ulist:
			s+=nodes[i][3]*zvariables["z2_" +str(i)]
		s+=zvariable
		prob += s>=total_pop*cover_pecentage/100.0

	prob.writeLP("_sclp_init3.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	if prob.status<=0:
		print "model unsolved..."
		return 0
	centersID=[-1 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	fselected=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='z': continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
				fselected.append(i)
	for k in fselected:
		for i in covered_units[k]:
			if node_groups[i]==-1: node_groups[i]=k
			if node_groups[i]>=0: 
				k2=node_groups[i]
				if nodedij[i][k] <nodedij[i][k2]: node_groups[i]=k
	update_district_info()
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	random.shuffle(ulist)
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if facilityCapacity[k]-district_info[k][1]>=nodes[i][3]:
				node_groups[i]=k
				district_info[k][1] +=nodes[i][3]
				break
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	random.shuffle(ulist)
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			#print "&",
			break
	update_district_info()
	return 1


#location set covering 
def lscp_lp_model(max_radius,cover_pecentage,time_limit,mipgap,lb): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpContinuous)
	zvariables={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpContinuous)

	obj=""
	for x in yvariables:
		obj +=yvariables[x]
	prob += obj

	if lb>0:
		s=""
		for k in centers:
			s+=yvariables["y_" +str(k)]
		prob +=s >= lb

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius*(random.random()+49.5)/50: continue
			s+=yvariables["y_" + str(j)]
		if cover_pecentage<100: 
			s-= zvariables["z_" +str(i)]
			prob +=s >= 0
		else:
			prob +=s >= 1

	if cover_pecentage<100:
		s=""
		for i in ulist:
			s+=nodes[i][3]*zvariables["z_" +str(i)]
		maxuc=total_pop*cover_pecentage/100
		prob += s>=maxuc
	#prob.writeLP("_lscp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	lb=0.0
	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	ylist=[]
	for v in prob.variables():
		if v.varValue < 0.00000001: continue
		items=v.name.split('_')
		i=int(items[1])
		if items[0]=='y':
			lb+=v.varValue
			if v.varValue>0.999:
				centersID[i]=facilityCandidate[i]
			else:
				ylist.append([i,v.varValue])
	maxcovered=total_pop*cover_pecentage/100
	ylist.sort(key=lambda x:-x[1])
	for k,y in ylist:
		centersID[k]=facilityCandidate[k]
		covered=0
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k] >=0:
					node_groups[i]=k
					if nodedij[i][k]<=max_radius: covered+=nodes[i][3]
					break
		if covered>=maxcovered: break
	update_district_info()
	return lb


def CFLP_CKFLP_model_init(max_radius, maxtime,mipgap, rand): #CFLP_CKFLP, i.e. split-demand 
	global node_groups
	global centersID
	global num_districts
	global district_info
	centers=range(num_districts)#facilityCandidate
	centers=[]
	ilist=[]
	supply=0
	try_count=0
	while supply<3*total_pop:
		if try_count>num_districts: break
		try_count+=1
		k=random.randint(0,num_districts-1)
		if len(ilist)>0:
			mind=min(nodedij[x][k] for x in ilist)
			if mind<max_radius*0.5: continue
		if k not in centers:
			centers.append(k)
			ilist.append(nearCustomer[k])
			supply+=facilityCapacity[k]
			try_count=0
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	for i in range(num_units):
		cnt=0
		for j in NearFacilityList[i]:
			if j not in centers: continue #range(num_districts): 
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, None, pulp.LpInteger) #
			if rand==0:
				costs["x_" +str(i)+ "_"+ str(j)]=nodedik[i][j]/nodes[i][3]
			else:
				costs["x_" +str(i)+ "_"+ str(j)]=nodedik[i][j]/nodes[i][3] *(random.random()+49.5)/50
			cnt+=1
			if cnt>=6: break
	yvariables={}
	for i in centers:#range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		if rand==0:
			costs["y_" +str(i)]=100000000
		else:
			costs["y_" +str(i)]=100000000*(random.random()+49.5)/50
	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	for y in yvariables:
		if costs[y]>0:
			obj += costs[y]*yvariables[y]
	prob +=obj

	for i in range(num_units):
		s=""
		for j in centers:#range(num_districts):
			ij="x_" +str(i)+ "_"+ str(j)
			if ij in xvariables:
				s+=xvariables[ij]
		prob +=s == nodes[i][3]
	#for i in range(num_units):
	#    for j in centers:#range(num_districts):
	#        s=xvariables["x_" +str(i)+ "_"+ str(j)] - nodes[i][3] *yvariables["y_" + str(j)]
	#        prob +=s <= 0

	for k in centers:#range(num_districts):
		s=""
		for i in range(num_units):
			ij="x_" +str(i)+ "_"+ str(k)
			if ij in xvariables:
				s+=xvariables[ij]
		s-=facilityCapacity[k]*(1+pop_deviation) * yvariables["y_" +str(k)]
		prob+=s <= 0
		
	#prob.writeLP("_cflp.lp")
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,maxSeconds=maxtime,gapRel =mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, options=['set mip tolerances mipgap ' +str(mipgap)])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=maxtime,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		arcpy_print("MIP solver status: " + str(prob.status))
		return -1

	cid=[]
	sol=[[-1,-1] for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.50):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				cid.append(i)
				#print v,v.varValue
				continue
			if items[0]=="h": continue
			k=int(items[2])
			if v.varValue>sol[i][1]:
				sol[i][0]=k
				sol[i][1]=v.varValue
	
	centersID=facilityCandidate[:]
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	for k in range(num_districts):
		if k not in cid:
			centersID[k]=-1
	for i in range(num_units):
		node_groups[i]=sol[i][0]
	update_district_info()
	return prob.status

def location_drop_lscp(max_radius): 
	global centersID
	global node_groups
	clist=[x for x in range(num_districts) if centersID[x]>=0 and x not in facility_inclusion_list]
	if clist==[]: return 0
	dlist=[]
	for k in clist:
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		cost=sum(-nodedik[x][k] for x in ulist)
		for i in ulist:
			d=min(nodedij[i][x] for x in clist if x!=k)
			cost+=d*nodes[i][3]
			#if d>max_radius: 
			#    assigned=0
			#    break
		dlist.append([k,cost])
	if len(dlist)==0: return 0 #fail
	dlist.sort(key=lambda x:x[1])
	r=random.random()
	idx=int(r*r*0.99*min(5,len(dlist)))
	k=dlist[idx][0]
	centersID[k]=-1
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	return 1

def drop_method_lscp(max_radius,cover_pecentage):
	global node_groups
	global centersID
	global all_solutions
	sol=[]
	node_groups=[NearFacilityList[x][0] for x in range(num_units)]
	centersID=facilityCandidate[:]
	if num_districts>num_units*5:
		for i in range(num_districts):
			if random.random()>0.1: centersID[i]=-1
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]==-1: continue
				node_groups[i]=k
				break
	while location_drop_lscp(max_radius):  #too slow for large instances, sampling ?
		update_cflpr_district_info()
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		cp=coverdemand*100.0/total_pop
		#print [biobjective,cp],
		if cp<cover_pecentage: break
		sol=[biobjective,centersID[:],node_groups[:]]
	if sol==[]: return
	node_groups=sol[2]
	centersID=sol[1]
	update_cflpr_district_info()
	
def lscp_sub_model(max_radius,cover_pecentage,time_limit,mipgap): 
	global centersID
	global node_groups
	dlist=select_region_lscp()
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	clist=get_cand_lscp_locations(dlist,ulist)
	centers=list(set(clist+dlist))
	for x in ulist:
		for k in NearFacilityList[x]:
			if nodedij[x][k]>max_radius: break
			if k==node_groups[x]: continue
			if centersID[k]>=0:
				node_groups[x]=k
				break
	prob = pulp.LpProblem("_lpcpr",pulp.LpMinimize)
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]

	costs={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
	zvariables={}
	for i in ulist:
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in yvariables:
		obj +=yvariables[x]
	prob += obj

	#cons 2

	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j] > max_radius: continue
			s+=yvariables["y_" + str(j)]
		if cover_pecentage<100:
			prob +=s - zvariables["z_" +str(i)] >= 0
		else:
			prob +=s >= 1


	#for i in ulist:
	#    for j in centers:
	#        if nodedij[i][j]>max_radius: continue
	#        s=yvariables["y_" + str(j)]+ zvariables["z_" +str(i)]
	#        prob +=s <= 1

	if cover_pecentage<100:
		covered_demand=0
		for x in range(num_units):
			k=node_groups[x]
			if k in dlist: continue
			if nodedij[x][k]<=max_radius: covered_demand+=nodes[x][3]
		s=""
		for i in ulist:
			s+=nodes[i][3]*zvariables["z_" +str(i)]
		maxuc=total_pop*cover_pecentage/100-covered_demand
		prob += s>=maxuc

	#prob.writeLP("_lscp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved..."
		return []
	for x in dlist: centersID[x]=-1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k] >=0:
				node_groups[i]=k
				break
	print len(dlist),len(centers),
	return 1

def lscp_matheuristic(max_radius,cover_pecentage,multi_start,maxloops):
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global best_centersID_global
	global best_solution_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	global facilityCost
	global facilityCapacity
	#global node_neighbors
	global region_pool
	global pool_index
	global is_spp_modeling
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	initialize_instance()
	max_loops_solution_not_improved=maxloops
	multi_start_count=multi_start
	print "num_facility:",max_num_facility
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	#facilityCapacity=[100000000 for x in range(num_districts)]
	pool_index=[[] for x in range(num_districts)]
	#for x in range(num_districts): facilityCost[x]=100000000
	not_improved_global=0
	loop=-1
	for idx in range(multi_start_count):
		#drop_method_lscp(max_radius,cover_pecentage)
		lb=lscp_lp_model(max_radius,cover_pecentage,150,0.0000000001,0)
		nf=int(lb+0.999)
		#lscp_lp_model(max_radius,cover_pecentage,150,0.0000000001,nf)
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		cp=coverdemand*100.0/total_pop
		nf=sum(1 for x in centersID if x>=0)
		print "init. sol.",idx, nf,biobjective,objective,objective_overload, str(int(cp))
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
	population.sort(key=lambda x:x[0]+x[-1]*10000)
	best_biobjective_global=population[0][0]
	best_centersID_global=population[0][1][:]
	best_solution_global=population[0][2][:]
	update_cflpr_district_info()
	best_biobjective_global=MAXNUMBER
	update_best_solution()
	all_solutions=population
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))* pow(r,1)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_cflpr_district_info()
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		lscp_sub_model(max_radius,cover_pecentage,20,0.0000000001)
		update_cflpr_district_info()
		update_best_solution()
		update_region_pool_all()

		s=""
		if best_biobjective_global<obj-0.000001:  #0.1%
			s="*"
			impp=((best_biobjective_global-obj)/best_biobjective_global)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: s="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop) + " Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		s+=" Current: "+str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_overload))
		s+=" Info: " +str(not_improved_global)+ " "+str(int(time.time()-t))
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		s+=" "+str(int(cp*10000)/100.0)
		arcpy_print(s)
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])#+x[-1]*10000)
		population=pop_selection(population)
		all_solutions=population
		if not_improved_global >= max_loops_solution_not_improved: break
		#if time.time()-t_ga > heuristic_time_limit:  break
	#post procedure
	ga_time=time.time()-t
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	if is_spp_modeling>=1:
		lscp_scp_model(max_radius,cover_pecentage,(time.time()-t)/5,0.00000001)
		#lspp_model(max_radius,cover_pecentage,heuristic_time_limit,0.00000001)
		update_district_info()
		update_best_solution()
		print "spp solution:",biobjective,objective_fcost,objective,objective_overload,time.time()-t
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
		population.sort(key=lambda x:x[0])
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	print "final solution:",biobjective,objective_fcost,objective,objective_overload,objective/total_pop,int(coverdemand*10000/total_pop)/100.0
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

def search_coverlist(idx,radius,cap):
	demand=0
	xlist=[]
	for i in nearCustomers[idx]:
		if nodedij[i][idx]>radius: break
		if demand+nodes[i][3]<=cap:
			demand+=nodes[i][3]
			xlist.append(i)
		else:
			break
	return xlist

def one_unit_move_cpcp(radius): #FA
	global node_groups
	global time_op
	#if objective_overload>=0: return 0
	t=time.time()
	klist=[x for x in range(num_districts) if district_info[x][4]>0]
	ulist=[x for x in range(num_units) if node_groups[x] in klist]
	if ulist==[]:
		ulist=[x for x in range(num_units) if nodedij[x][node_groups[x]]>=radius*0.9]
	random.shuffle(ulist)
	#ulist+=[x for x in range(num_units)]
	improved=0
	for nid in ulist:
		rid=node_groups[nid]
		demand=nodes[nid][3]
		klist=[x for x in NearFacilityList[nid] if centersID[x]>=0]
		klist=klist[:8]
		for k in klist:
			#if nodedij[nid][k]>radius: continue
			overload1=district_info[k][4]+district_info[rid][4]
			overload2=max(0, district_info[rid][1]-demand-facilityCapacity[rid])
			overload2+=max(0, district_info[k][1]+demand-facilityCapacity[k])
			if overload1 < overload2: continue
			if overload1 == overload2 and nodedij[nid][k]>=nodedij[nid][rid]: continue
			#if overload2==overload1: print nodedij[nid][k]-nodedij[nid][rid],
			node_groups[nid]=k
			update_district_info()
			improved=1
			break
	update_district_info()
	time_op[0]+=time.time()-t
	return improved

def cpcp_bs(num_f,capacity,r1,r2,gap):
	global centersID
	global node_groups
	global district_info
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]

	max_radius=r2
	min_radius=r1
	'''n=num_districts/num_f
	for x in range(num_units):
		k=NearFacilityList[x][n]
		d=nodedij[x][k]
		if d>max_radius: max_radius=d
	for k in range(num_districts):
		i=nearCustomer[k]
		r=nodedij[i][k]
		if r<min_radius: min_radius=r
	min_radius*= (20+random.random())/20'''
	print "initial R", min_radius, max_radius

	t=time.time()
	best_radius=0.0
	best_locations=[]
	best_solution=[]
	loop=0
	t=time.time()
	sta=1
	while 1:
		loop+=1
		radius=min_radius + (max_radius-min_radius)/2
		s="loop: "+str(loop)+" min: " + str(min_radius) + " max: " +str(max_radius) + " current: " +str(radius)
		#sta=cover_100p_model(num_f,radius,capacity,10000.0,0.999)
		sta=mclp_100p_model(num_f,radius,capacity,heuristic_time_limit/2,0.9)
		#sta=mclp_cpcp_model(num_f,radius,capacity,10000.0,0.00000001)
		#sta=sclp_cpcp_model(num_f,capacity,radius,10000,0.999)       
		if sta<1:
			min_radius=radius
		if sta==1:
			max_radius= max(nodedij[x][node_groups[x]] for x in range(num_units) )
			if max_radius>radius+0.001: 
				print s+" feasible? " +str(sta)
				print "warning:", max_radius,radius
				break
			best_locations=centersID[:]
			best_solution=node_groups[:]
		s+=" feasible? " +str(sta) + " gap:"+ str(100.0*(max_radius-min_radius)/max_radius)  +"% time: " + str(time.time()-t)
		print s  
		if (max_radius-min_radius)/max_radius<=gap: break
		if time.time()-t> heuristic_time_limit: break
	centersID=best_locations[:]
	node_groups=best_solution[:]
	if capacity==0:
		pmp_mip_model(num_f,max_radius,100,200,0.001)
	update_district_info()
	return max_radius

def cflpr_model(max_radius2,max_radius,cover_pecentage,numf,time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	cflp_max_service_radius=max_radius2
	cflp_service_radius_preference=max_radius
	cflp_min_service_coverage_percentage=cover_pecentage
	
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*travel_distance_weight
			d=nodedij[i][j]
			if envy_service_objective==1 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				xcost["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	#zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			obj+=costs["x_" +str(i)+ "_"+ str(j)]*xvariables["x_" +str(i)+ "_"+ str(j)]
	#obj+=100000000*zvariable
	prob += obj

	#cons 2
	for i in ulist:
		if nodes[i][3]<=0: continue
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		if len(s)==0:
			print "node", nodes[i][4],"cannot be covered by any facility!!!",nodes[i]
			print "dist(ij) > max_radius:", min(nodedij[i]),">", max_radius2 
			exit(0)
		prob += s==1
	for i in ulist:
		if nodes[i][3]<=0:
			k=NearFacilityList[i][0]
			s=xvariables["x_" +str(i)+ "_"+ str(k)]
			prob += s==1
	for k in centers:
		for i in ulist:
			if nodedij[i][k]>max_radius2: continue
			prob += xvariables["x_" +str(i) + "_"+ str(k) ] <= yvariables["y_" +str(k)]

	for k in centers:
		s=""
		for i in ulist:
			if nodedij[i][k]>max_radius2: continue
			s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
		if facilityMinimumCapacity>0:
			prob+=s >= facilityMinimumCapacity*yvariables["y_" +str(k)]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)]
		prob += s <= 0

	s=""
	for k in centers:
		s+= facilityCapacity[k]*yvariables["y_" +str(k)]
	prob += s >= total_pop

	if cover_pecentage>0:
		s=""
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
		prob += s >=total_pop*cover_pecentage/100
	'''else:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius:
					prob += xvariables["x_" +str(i) + "_"+ str(j)] == 0'''
	if numf>0:
		s=""
		for j in centers:
			s+=yvariables["y_" +str(j)]
		prob += s==numf
	if max_facility_cost>0:
		s=""
		for k in range(num_districts):
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		prob += s <= max_facility_cost
		
	for j in facility_inclusion_list:
		s=yvariables["y_" +str(j)]
		prob += s==1

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0

	prob.writeLP("_cflpr2.lp")
	initvalues=cflp_mst()
	for x,v in initvalues:
	   #items=x.split("_")
	   if x.find("y")==0:  yvariables[x].setInitialValue(v)       
	   if x.find("x")==0:  
		   try: 
			  xvariables[x].setInitialValue(v)
		   except:
			  pass
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_zero_demand()
	update_cflpr_district_info()
	coverdemand=0
	coverdemand2=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		if nodedij[i][k]>max_radius2: coverdemand2+=nodes[i][3]
	print "model solution:",biobjective,objective_fcost,objective,objective_overload,coverdemand2,int(coverdemand*10000/total_pop)/100.0
	all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost])
	all_solutions.sort(key=lambda x:x[0])
	return 1

def uflp_model(max_radius2,max_radius,cover_pecentage,time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	prob = pulp.LpProblem("uflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*travel_distance_weight
			d=nodedij[i][j]
			if envy_service_objective==1 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for x in xvariables:
		obj +=costs[x]* xvariables[x]
	#for i in ulist:
	#    for j in centers:
	#        if nodedij[i][j]>max_radius2: continue
	#        obj+=costs["x_" +str(i)+ "_"+ str(j)]*xvariables["x_" +str(i)+ "_"+ str(j)]
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		if len(s)==0:
			print "node", nodes[i][4],"cannot be covered by any facility!!!",nodes[i]
			print "dist(ij) > max_radius:", min(nodedij[i]),">", max_radius2 
			exit(0)
		prob += s==1

	for k in centers:
		s=""
		for i in ulist:
			if nodedij[i][k]>max_radius2: continue
			s+= xvariables["x_" +str(i) + "_"+ str(k) ]
		s-= num_units*yvariables["y_" +str(k)]
		prob += s <= 0
	for k in centers:
		for i in ulist:
			if nodedij[i][k]>max_radius2: continue
			prob += xvariables["x_" +str(i) + "_"+ str(k) ] <= yvariables["y_" +str(k)]
	if adaptive_number_of_facilities==0 and max_num_facility>0:
		s=""
		for x in yvariables:
			s += yvariables[x]
		prob += s<=max_num_facility
		
	if cover_pecentage>0:
		s=""
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius2: continue
				if nodedij[i][j]>max_radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
		prob += s >= total_pop*cover_pecentage/100

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0

	prob.writeLP("_uflp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_cflpr_district_info()
	coverdemand=0
	coverdemand2=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		if nodedij[i][k]>max_radius2: coverdemand2+=nodes[i][3]
	print "model solution:",biobjective,objective_fcost,objective,objective_envy,objective_overload,coverdemand2,int(coverdemand*10000/total_pop)/100.0
	all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost])
	all_solutions.sort(key=lambda x:x[0])
	return 1

def me_uflp_model(capacity, time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	prob = pulp.LpProblem("me_uflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*travel_distance_weight
			d=nodedij[i][j]
			if envy_service_objective==1 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==8: 
				costs["x_" +str(i)+"_"+str(j)]=nodes[i][3]*math.exp(2*d/envy_service_distance)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	if capacity==1:
		zvariable=pulp.LpVariable("z", 0, None, pulp.LpInteger)
	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for x in xvariables:
		obj +=costs[x]* xvariables[x]
	if capacity==1:
		obj+=100000000*zvariable
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1

	for k in centers:
		s=""
		for i in ulist:
			s+= xvariables["x_" +str(i) + "_"+ str(k) ]
		s-= num_units*yvariables["y_" +str(k)]
		prob += s <= 0

	for k in centers:
		for i in ulist:
			s= xvariables["x_" +str(i) + "_"+ str(k) ]
			prob += s <= yvariables["y_" +str(k)]
	if capacity==1:
		for k in centers:
			s=""        
			for i in ulist:
				s += nodes[i][3] * xvariables["x_" +str(i)+"_"+str(k)]
			s -= facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0

	if facilityMinimumCapacity>0:
		for k in centers:
			s=""
			for i in ulist:
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			prob += s >= facilityMinimumCapacity*yvariables["y_" +str(k)]
	if facilityMaximumCapacity>0:
		for k in centers:
			s=""
			for i in ulist:
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			prob += s <= facilityMaximumCapacity*yvariables["y_" +str(k)]

	'''for k in centers:
		s=""
		for i in ulist:
			s+= xvariables["x_" +str(i) + "_"+ str(k) ]       
		prob += s <= num_units*yvariables["y_" +str(k)]'''

	if max_facility_cost>0:
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		if capacity==1:
			prob += s-zvariable <= max_facility_cost
		if capacity==0:
			prob += s <= max_facility_cost
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0
	

	prob.writeLP("_ce_uflp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='z':continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_cflpr_district_info()
	return 1

def cflpr_lp_model(max_radius2,max_radius,cover_pecentage,numf,time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	prob = pulp.LpProblem("cflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	'''if num_districts>10*numf:
		random.shuffle(centers)
		centers=centers[:10*numf]'''
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpContinuous)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]#*(95+random.random()*10)/100.0
	yvariables={}
	for i in centers:
		#yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpContinuous)
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	#zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	obj=""
	for i in ulist:
		 for j in centers:
			if nodedij[i][j]>max_radius2: continue
			obj+=costs["x_" +str(i)+ "_"+ str(j)]*xvariables["x_" +str(i)+ "_"+ str(j)]
	#s=obj
	if fixed_cost_obj==1:    
		for x in yvariables:
			obj +=costs[x]* yvariables[x] #*(random.random()+49.5)/50
	#obj+=100000000*zvariable
	prob += obj
	
	##prob += s >= envy_service_distance*total_pop
	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius2: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1

	if pop_deviation==0:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]>max_radius2: continue
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			s-= facilityCapacity[k]*yvariables["y_" +str(k)]
			prob += s <= 0
	if pop_deviation>0:
		for k in centers:
			s=""
			for i in ulist:
				if nodedij[i][k]>max_radius2: continue
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			prob += s <= (100+pop_deviation)/100.0*facilityCapacity[k]*yvariables["y_" +str(k)]
			prob += s >= (100-pop_deviation)/100.0*facilityCapacity[k]*yvariables["y_" +str(k)]

	if cover_pecentage>0:
		s=""
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
		prob += s >=total_pop*cover_pecentage/100
	if max_facility_cost>0:
		s=""        
		for x in yvariables:
			s +=costs[x]* yvariables[x] #*(random.random()+49.5)/50
		prob += s <= max_facility_cost  
	if numf>0:
		s=""
		for j in centers:
			s+= yvariables["y_" +str(j)]
		prob += s==numf
	#warmStart=True,
	prob.writeLP("_cflpr_lr.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(mipgap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(msg=solver_message, timeLimit=time_limit,options=[("MIPGap",mipgap)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return -1
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	max_xij=[0.0 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.000001):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				if v.varValue>max_xij[i]:
					node_groups[i]=int(items[2])
					max_xij[i]=v.varValue 
	update_cflpr_district_info()
	return 1

def cflpr_envy_model(max_radius,rec_radius,cover_pecentage,numf,time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	prob = pulp.LpProblem("pcp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*travel_distance_weight
			if envy_service_objective==1 and nodedij[i][j]>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)] += nodes[i][3]*envy_objective_weight*(nodedij[i][j]-envy_service_distance)*(nodedij[i][j]-envy_service_distance)
			if envy_service_objective==4 and nodedij[i][j]>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)] += nodes[i][3]*envy_objective_weight*(nodedij[i][j]-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	#zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	fvariables={}
	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)

	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			obj+=costs["x_" +str(i)+ "_"+ str(j)]*xvariables["x_" +str(i)+ "_"+ str(j)]
	#obj+=100000000*zvariable
	prob += obj

	#cons 2
	for i in ulist:
		if nodes[i][3]<=0: continue
		s=""
		for j in centers:
			if nodedij[i][j]>max_radius: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		if len(s)==0:
			print "node", nodes[i][4],"cannot be covered by any facility!!!",nodes[i]
			print "dist(ij) > max_radius:", min(nodedij[i]),">", max_radius 
			exit(0)
		prob += s==1
	'''for i in ulist:
		if nodes[i][3]<=0:
			k=NearFacilityList[i][0]
			s=xvariables["x_" +str(i)+ "_"+ str(k)]
			prob += s==1'''

	for k in centers:
		s=""
		for i in ulist:
			if nodedij[i][k]>max_radius: continue
			s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)]
		prob += s <= 0

	s=""
	for k in centers:
		s+= facilityCapacity[k]*yvariables["y_" +str(k)]
	prob += s >= total_pop

	if cover_pecentage<100:
		s=""
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>rec_radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
		prob += s >=total_pop*cover_pecentage/100
	'''else:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>rec_radius:
					prob += xvariables["x_" +str(i) + "_"+ str(j)] == 0'''
	if numf>0:
		s=""
		for j in centers:
			s+=yvariables["y_" +str(j)]
		prob += s==numf

	for j in facility_inclusion_list:
		s=yvariables["y_" +str(j)]
		prob += s==1

	if spatial_contiguity==1:
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					if nodedij[i][k]>max_radius: continue
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units * xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					if nodedij[j][k]>max_radius: continue
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= num_units* xvariables["x_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
		for i in range(num_units):
			for k in range(num_districts):
				if nodedij[i][k]>max_radius: continue
				if facilityCandidate[k]!=i:
					s=""
					for j in node_neighbors[i]:
						s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
					s-= xvariables["x_" +str(i)+ "_"+ str(k)]
					prob += s >= 0

	prob.writeLP("_cflpr2.lp")
	initvalues=cflp_mst()
	for x,v in initvalues:
	   #items=x.split("_")
	   if x.find("y")==0:  yvariables[x].setInitialValue(v)       
	   if x.find("x")==0:  
		   try: 
			  xvariables[x].setInitialValue(v)
		   except:
			  pass
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	update_zero_demand()
	update_cflpr_district_info()
	coverdemand=0
	coverdemand2=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=rec_radius: coverdemand+=nodes[i][3]
		if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
	print "model solution:",biobjective,objective_fcost,objective,objective_overload,coverdemand2,int(coverdemand*10000/total_pop)/100.0
	all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost])
	all_solutions.sort(key=lambda x:x[0])
	return 1

def location_drop_cflpr(max_radius2,max_radius,cover_pecentage): 
	global centersID
	global node_groups
	clist=[x for x in range(num_districts) if centersID[x]>=0 and x not in facility_inclusion_list]
	if clist==[]: return 0
	dlist=[]
	random.shuffle(clist)
	for k in clist:
		ids=centersID[:]
		ids[k]=-1
		ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x]==k]
		ulist.sort(key=lambda x:-x[1])
		savings=district_info[k][2]
		savings+=facilityCost[k]
		caplist=[facilityCapacity[x]-district_info[x][1] for x in range(num_districts)]
		caplist[k]=0
		assigned=0
		for x,y in ulist:
			assigned=0
			for r in NearFacilityList[x]:
				if centersID[r]<0: continue
				if r==k: continue
				if y<=caplist[r]:
					savings-=nodedik[x][r]
					caplist[r]-=y
					assigned=1
					break
			if assigned==0: break
		if assigned==1: dlist.append([k,savings])
	if len(dlist)==0: return -1
	dlist.sort(key=lambda x:-x[1])
	update_district_info()
	f_del=0
	tabu=[]
	status=0
	while 1:
		if len(dlist)<1: break
		temp=[centersID[:],node_groups[:]]
		r=random.random()
		idx=int(r*0.999*min(3,len(dlist)))
		k=dlist[idx][0]
		del dlist[idx]
		if k in tabu: continue
		centersID[k]=-1
		ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x]==k]
		ulist.sort(key=lambda x:-x[1])
		caplist=[district_info[x][3]-district_info[x][1] for x in range(num_districts)]
		caplist[k]=0
		assigned=1
		for x,y in ulist:
			assigned=0
			for r in NearFacilityList[x]:
				if centersID[r]<0: continue
				if y<=caplist[r]:
					caplist[r]-=y
					node_groups[x]=r
					assigned=1
					if r not in tabu: tabu.append(r)
					break
			if assigned==0: break
		if assigned==0:
			centersID=temp[0][:]
			node_groups=temp[1][:]
			update_cflpr_district_info()
			return status
		update_cflpr_district_info()
		#print objective,objective_fcost,objective_overload
		status=1
		f_del+=1
		if f_del>=len(clist)/20 or f_del>=10: break
		supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)
		if supply<=total_pop*3: break
		nf=sum(1 for x in centersID if x>=0)
		if adaptive_number_of_facilities==0 and nf==max_num_facility:
			break
		if adaptive_number_of_facilities==1 and max_facility_cost>0:
			fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
			if fc<=max_facility_cost:
				break
	return status

def drop_method_cflpr(max_radius2,max_radius,cover_pecentage):
	global node_groups
	global centersID
	global all_solutions
	sol=[]
	node_groups=[NearFacilityList[x][0] for x in range(num_units)]
	centersID=facilityCandidate[:]
	#for x in range(num_districts):
	#    if x not in node_groups: centersID[x]=-1
	if total_supply>10*total_pop:
		centersID=[-1 for x in range(num_districts)]
		sampling=1
		min_nf=int(total_pop*num_districts/total_supply)
		#centers=k_medoids_cflpr_sampling(min_nf*10)
		clist=range(num_districts)
		random.shuffle(clist)
		clist=clist[:min_nf*10]
		centers=list(set(clist+facility_inclusion_list))
		for k in centers: centersID[k]=facilityCandidate[k]
	if total_supply>total_pop*1000:
		supply=0
		centersID=[-1 for x in range(num_districts)]
		try_count=0
		while supply<total_pop*10:
			k=random.randint(0,num_districts-1)
			if try_count>=num_districts/2: break
			if centersID[k]>=0: continue
			if supply>0:
				u=nearCustomers[k][0]
				min_dis=min(nodedij[u][x] for x in range(num_districts) if centersID[x]>=0)
				if min_dis<max_radius*0.6: 
					try_count+=1
					continue
			supply+=facilityCapacity[k]
			centersID[k]=facilityCandidate[k]
			try_count=0
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]==-1: continue
			node_groups[i]=k
			break 
	update_cflpr_district_info()
	while 1:
		sol=[centersID[:],node_groups[:]]
		#print [x for x in centersID if x>=0]        
		sta=location_drop_cflpr(max_radius2,max_radius,cover_pecentage)  #too slow for large instances, sampling ?
		update_cflpr_district_info()
		#update_district_info()
		if sta<=0: break
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		cp=coverdemand*100.0/total_pop
		if adaptive_number_of_facilities==1 and cp<cover_pecentage: break
		#print biobjective, objective,objective_fcost,objective_overload, cp
		sol=[biobjective,centersID[:],node_groups[:]]
		#print sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0), [k for k in centersID if k>=0]
		
		nf=sum(1 for x in centersID if x>=0)
		if adaptive_number_of_facilities==0 and nf <= max_num_facility: 
			sol=[biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0]
			break
		if adaptive_number_of_facilities==1 and max_facility_cost>0:
			fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
			if fc<= max_facility_cost:           
				sol=[biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0]
				break
			
	#if len(sol)>0:
	#    node_groups=sol[2][:]
	#    centersID=sol[1][:]
	#    update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	if adaptive_number_of_facilities==0 and nf > max_num_facility:
		droplist=[]
		dlist=[x for x in range(num_districts) if centersID[x] >=0]
		while len(dlist) >max_num_facility:
			random.shuffle(dlist)
			k=dlist[0]
			if k in facility_inclusion_list: continue
			dlist.remove(k)
			droplist.append(k)
			#print [len(dlist),len(droplist)],
		#print droplist
		for x in droplist: centersID[x]=-1
		ulist= [x for x in range(num_units) if node_groups[x] in droplist]
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				node_groups[i]=k
				break
		#update_cflpr_district_info(max_radius,cover_pecentage)
		update_district_info()
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		cp=coverdemand*100.0/total_pop
	return 1

def drop_method_uflp_envy1(max_radius2,max_radius,cover_pecentage):
	global node_groups
	global centersID
	node_groups=[NearFacilityList[x][0] for x in range(num_units)]
	centersID=facilityCandidate[:]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]==-1: continue
			node_groups[i]=k
			break 
	max_radius2,max_radius,cover_pecentage
	while 1:
		dropList=[]
		rlist=[x for x in range(num_districts) if centersID[x]>=0]
		for k in rlist:
			savings=facilityCost[k]
			covered_new=0
			ulist=[x for x in range(num_units) if node_groups[x]==k]
			for i in ulist:
				savings+=nodedik[i][k]
				if nodedij[i][k] > max_radius2:
					savings+= penalty_on_demand*nodes[i][3]
				if nodedij[i][k] <= max_radius:
					covered_new+=nodes[i][3]
				if envy_service_objective==1 and nodedij[i][k]>envy_service_distance:
					savings+= nodes[i][3] * envy_objective_weight*(nodedij[i][k]-envy_service_distance)*(nodedij[i][k]-envy_service_distance)
				if envy_service_objective==4 and nodedij[i][k]>envy_service_distance:
					savings+= nodes[i][3] * envy_objective_weight*(nodedij[i][k]-envy_service_distance)
				for j in NearFacilityList[i]:
					if j!=k and centersID[j]>=0:
						savings -= nodedik[i][j]
						if envy_service_objective==1 and nodedij[i][j]>envy_service_distance:
							savings -= nodes[i][3] * envy_objective_weight*(nodedij[i][j]-envy_service_distance)*(nodedij[i][j]-envy_service_distance)
						if envy_service_objective==4 and nodedij[i][j]>envy_service_distance:
							savings -= nodes[i][3] * envy_objective_weight*(nodedij[i][j]-envy_service_distance)
						if nodedij[i][j] > max_radius2:
							savings -= penalty_on_demand*nodes[i][3]
						break
			covered=0
			covered_old=0
			for i in range(num_units):
				k1=node_groups[i]
				if k1!=k and nodedij[i][k1]<=max_radius:
					covered += nodes[i][3]
				else:
					covered_old += nodes[i][3]

			min_covered=total_pop*cover_pecentage/100
			savings += max(0, min_covered- covered - covered_old )*penalty_on_demand
			savings -= max(0, min_covered- covered - covered_new )*penalty_on_demand
			if savings>0: dropList.append([k,-savings])
		
		if len(dropList)<1: break
		dropList.sort(key=lambda x: x[1])
		idx=0
		if len(dropList)>3: 
			idx=random.randint(0, 3)
		k=dropList[idx][0]
		centersID[k]=-1
		ulist= [x for x in range(num_units) if node_groups[x]==k]
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				node_groups[i]=k
				break
	return 1

def add_select(n):
	ilist=[x for x in range(num_units) if node_groups[x]<0]
	idislist=[]
	for i in ilist:
		dis=0.0
		count=0
		for k in NearFacilityList[i]:
			u=nearCustomer[k]
			if node_groups[u]>=0: continue
			dis+=nodedij[i][k]
			count+=1
			if count>=n:break
		idislist.append([i,dis])
	idx=0
	if len(idislist)>1:
		idx=random.randint(0,min(2,len(idislist)-1))
		idislist.sort(key=lambda x:-x[1])
	u=idislist[idx][0]
	k_select=-1
	for k in NearFacilityList[u]:
		if centersID[k]>=0: continue
		u=nearCustomer[k]
		if node_groups[u]>=0: continue
		k_select=k
		break
	return k_select

def add_method_cflpr(max_radius,cover_pecentage):
	global node_groups
	global centersID
	global all_solutions
	global district_info
	#avg_d=total_pop/num_units
	#avg_s=total_supply/num_districts
	#avg_grids=avg_s/avg_d*6
	avg_nf=int(4*total_supply/total_pop)
	centersID=[-1 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	uncovered=0
	max_uncovered=total_pop*(100-cover_pecentage)/100
	#max_uncovered=0
	nf=total_pop*num_districts/total_supply
	max_uncovered_local=max_uncovered/nf*4
	while 1:
		if -1 not in node_groups: break
		k=add_select(avg_nf)
		supply=facilityCapacity[k]
		ulist=[]
		for i in nearCustomers[k]:
			if node_groups[i]>=0: continue
			if supply<nodes[i][3]: break
			ulist.append(i)
			supply-=nodes[i][3]
		u=ulist[0]
		klist=[x for x in range(num_districts) if centersID[x]<0 and facilityCapacity[x]>=facilityCapacity[k] and nearCustomer[x] in ulist and nodedij[u][x]<=max_radius]
		min_dis=MAXNUMBER
		for x in klist:
			dis= sum(nodedij[u][x] for u in ulist)
			if dis<min_dis:
				min_dis=dis
				k=x
		centersID[k]=facilityCandidate[k]
		uncovered_local=0
		assigned=0 
		alist=[]
		uncovered=0
		for i in range(num_units):
			if node_groups[i]<0: continue
			j=node_groups[i]
			if nodedij[i][j]>max_radius: uncovered+=nodes[i][3]
		for i in ulist:
			if nodedij[i][k]>1.5*max_radius: continue
			if nodedij[i][k]>max_radius:
				if uncovered_local+nodes[i][3]>max_uncovered_local: continue
				if uncovered+nodes[i][3]>max_uncovered: continue
				uncovered_local+=nodes[i][3]
				uncovered+=nodes[i][3]
			node_groups[i]=k
			alist.append(i)
			assigned=1
		#print ulist
		#print alist
		update_cflpr_district_info()
		ilist=[x for x in range(num_units) if node_groups[x]<0]
		random.shuffle(ilist)
		for i in ilist:
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				if nodedij[i][k]>max_radius: break
				if nodes[i][3]+ district_info[k][1] >facilityCapacity[k]: continue
				node_groups[i]=k
				assigned = 1
				district_info[k][1]+=nodes[i][3]
				break 
		for i in range(num_units):
			if node_groups[i]>=0: continue
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				if nodedij[i][k]>max_radius: break
				if nodes[i][3]+ district_info[k][1] >facilityCapacity[k]: continue
				node_groups[i]=k
				assigned = 1
				#print "-",
				district_info[k][1]+=nodes[i][3]
				break 
		if assigned == 0: break

		#supply=facilityCapacity[k]
		#for i in nearCustomers[k]:
		#    if node_groups[i]>=0: continue
		#    if supply<nodes[i][3]: break
		#    if nodedij[i][k]>max_radius:
		#        if uncovered+nodes[i][3]>max_uncovered: break
		#        uncovered+=nodes[i][3]
		#    node_groups[i]=k
		#    supply-=nodes[i][3]
	ilist=[x for x in range(num_units) if node_groups[x]<0]
	print sum(nodes[x][3] for x in ilist),#ilist, 
	if ilist!=[]:
		for i in ilist:
			 for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				node_groups[i]=k
				break 
	update_cflpr_district_info()
	#update_cflpr_centers(max_radius,cover_pecentage)
	#if objective_overload>0: one_unit_move()
	sol=[]
	while 0:
		CID1=centersID[:]
		location_drop_cflpr(max_radius,cover_pecentage)  #too slow for large instances, sampling ?
		if CID1==centersID[:]: break
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=max_radius: coverdemand+=nodes[i][3]
		cp=coverdemand*100.0/total_pop
		if adaptive_number_of_facilities==1 and cp<cover_pecentage: break
		sol=[biobjective,centersID[:],node_groups[:]]
		nf=sum(1 for x in centersID if x>=0)
		if adaptive_number_of_facilities==0 and nf == max_num_facility: 
			sol=[biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0]
			break
		if objective_overload>0:
			one_unit_move()
	if sol!=[]: 
		node_groups=sol[2]
		centersID=sol[1]
		update_district_info()

def add_method_cflpr2(max_radius,cover_pecentage):
	global node_groups
	global centersID
	global all_solutions
	global district_info
	avg_nf=int(4*total_supply/total_pop)
	centersID=[-1 for x in range(num_districts)]
	node_groups=[-1 for x in range(num_units)]
	uncovered=0
	max_uncovered=total_pop*(100-cover_pecentage)/100
	#max_uncovered=0
	nf=total_pop*num_districts/total_supply
	max_uncovered_local=max_uncovered/nf*3
	while 1:
		if -1 not in node_groups: break
		k=add_select(avg_nf)
		if k<0: break
		supply=facilityCapacity[k]
		ulist=[]
		for i in nearCustomers[k]:
			if nodedij[i][k]>max_radius*2: continue
			if node_groups[i]>=0: continue
			if supply<nodes[i][3]: break
			ulist.append(i)
			supply-=nodes[i][3]
		u=ulist[0]
		klist=[x for x in range(num_districts) if centersID[x]<0 and facilityCapacity[x]>=facilityCapacity[k] and nearCustomer[x] in ulist and nodedij[u][x]<=max_radius]
		min_dis=MAXNUMBER
		for x in klist:
			dis= sum(nodedij[u][x] for u in ulist)
			if dis<min_dis:
				min_dis=dis
				k=x
		centersID[k]=facilityCandidate[k]
		uncovered_local=0
		uncovered=0
		for i in range(num_units):
			if node_groups[i]<0: continue
			j=node_groups[i]
			if nodedij[i][j]>max_radius: uncovered+=nodes[i][3]
		assigned=0 
		for i in ulist:
			if nodedij[i][k]>2*max_radius: continue
			if nodedij[i][k]>max_radius:
				if uncovered_local+nodes[i][3]>max_uncovered_local: continue
				if uncovered+nodes[i][3]>max_uncovered: continue
				uncovered_local+=nodes[i][3]
				uncovered+=nodes[i][3]
			node_groups[i]=k
			assigned=1
		update_district_info()
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				if nodedij[i][k]>max_radius: break
				if nodes[i][3]+ district_info[k][1] >facilityCapacity[k]: continue
				node_groups[i]=k
				assigned = 1
				district_info[k][1]+=nodes[i][3]
				break 
		ilist=[x for x in range(num_units) if node_groups[x]<0]
		random.shuffle(ilist)
		for i in ilist:
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				if nodedij[i][k]>max_radius: break
				if nodes[i][3]+ district_info[k][1] >facilityCapacity[k]: continue
				node_groups[i]=k
				assigned = 1
				district_info[k][1]+=nodes[i][3]
				break 
		if assigned == 0: break

	ilist=[x for x in range(num_units) if node_groups[x]<0]
	print sum(nodes[x][3] for x in ilist),#ilist, 
	if ilist!=[]:
		for i in ilist:
			 for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				node_groups[i]=k
				break 

def update_cflpr_district_info():
	global biobjective
	global objective
	global objective_pentalty_on_rmax
	global objective_pentalty_on_covering  
	global objective_pentalty_on_overload
	global objective_envy
	global objective_covered
	global objective_rmax_not_covered
	#objective*=travel_distance_weight
	update_district_info()
	if envy_service_objective==9: #ede
		obj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]            
			obj+=nodes[i][3]*math.exp(envy_objective_weight*d/envy_service_distance)
		biobjective=obj
		return
	objective_pentalty_on_overload=objective_overload*penalty_on_demand
	if cflp_min_service_coverage_percentage>0:    
		covered=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=cflp_service_radius_preference: covered+=nodes[i][3]
		objective_covered=covered
		objective_pentalty_on_covering= max(0, total_pop*cflp_min_service_coverage_percentage/100.0-covered)*penalty_on_demand
	covered2=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]>cflp_max_service_radius: covered2+=nodes[i][3]
	objective_rmax_not_covered=covered2
	objective_pentalty_on_rmax=covered2*penalty_on_demand
	#penalty_demands =objective_overload
	#penalty_demands+= max(0, total_pop*cover_pecentage/100-covered)
	#penalty_demands+=covered2
	#penalty=penalty_on_demand
	#biobjective=objective+penalty*penalty_demands
	biobjective=objective*travel_distance_weight+objective_pentalty_on_overload+objective_pentalty_on_rmax+objective_pentalty_on_covering
	if facilityMinimumCapacity>0:
		lowload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			lowload += max(0, facilityMinimumCapacity-district_info[k][1])
		biobjective+=penalty_on_demand*lowload
	if facilityMaximumCapacity>0:
		overload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			overload += max(0, district_info[k][1]-facilityMaximumCapacity)
		biobjective+=penalty_on_demand*overload

	if fixed_cost_obj==1: biobjective += objective_fcost
	if max_facility_cost>0:
		fc=0.0
		for k in range(num_districts):
			if centersID[k]>=0:
				fc+=facilityCost[k]
		extra=max(0, fc-max_facility_cost)
		biobjective+=penalty_on_demand*extra
	if envy_service_objective==1:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
		objective_envy=envyobj
		biobjective += envyobj
	if envy_service_objective==4:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
		objective_envy=envyobj
		biobjective += envyobj
	if envy_service_objective==8: #min sum(di*di)
		biobjective = 0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			biobjective += d*d
	if envy_service_objective==9:
		biobjective = 0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			biobjective += math.exp(envy_objective_weight*d/envy_service_distance)

def update_envy_district_info():
	global biobjective
	global objective_envy
	update_district_info()
	if envy_service_objective==9: #ede
		obj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]            
			obj+=nodes[i][3]*math.exp(envy_objective_weight*d/envy_service_distance)
		biobjective=obj
		return
	penalty=penalty_on_demand
	biobjective=objective*travel_distance_weight+objective_fcost*fixed_cost_obj
	biobjective+=penalty_on_demand*objective_overload    
	if max_facility_cost>0:    
		fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		efcost=max(0,fcost-max_facility_cost)
		biobjective+=efcost*penalty
	if facilityMinimumCapacity>0:
		lowload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			lowload += max(0, facilityMinimumCapacity-district_info[k][1])
		biobjective+=penalty_on_demand*lowload
	if facilityMaximumCapacity>0:
		overload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			overload += max(0, district_info[k][1]-facilityMaximumCapacity)
		biobjective+=penalty_on_demand*overload
	   
	if envy_service_objective==1:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
		objective_envy=envyobj
		biobjective += envyobj
	if envy_service_objective==4:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
		objective_envy=envyobj
		biobjective += envyobj
		#print "envyobj",envyobj
   
def update_cflpr_centers(r,p):
	global node_groups
	global centersID
	global time_update_centers
	t=time.time()
	centers=[x for x in range(num_districts) if centersID[x]>=0 and x not in facility_inclusion_list]
	random.shuffle(centers)
	for k in centers:
		newk=update_cflpr_center(k,r,p)
		if newk==k: continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		for x in ulist: node_groups[x]=newk
		centersID[k]=-1
		centersID[newk]=facilityCandidate[newk]
		#print "a center updated!"
	time_update_centers+=time.time()-t

def update_cflpr_center(k,r,p):
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	covered=0
	for i in ulist:
		j=node_groups[i]
		if nodedij[i][k]<r: 
			covered+=nodes[i][3]
	demand=sum(nodes[x][3] for x in ulist)
	best_cost=sum(nodedik[x][k] for x in ulist)
	best_center=k
	uid=nearCustomer[k]
	centers=[]
	for x in NearFacilityList[uid]:
		if centersID[x]<0: centers.append(x)
		if len(centers)>=min(20,len(ulist)): break
	for i in centers:
		if i==k: continue
		if facilityCapacity[i]<demand and facilityCapacity[k]<facilityCapacity[i]: continue
		cost=sum(nodedik[x][i] for x in ulist)
		if cost>=best_cost: continue
		covered3=0
		for j in ulist:
			if nodedij[j][i]<r:covered3+=nodes[j][3]
		if covered3<covered: continue 
		best_cost=cost
		best_center=i
	return best_center

cflpr_search_time=[0.0,0.0,0.0,0.0,0.0]
cflpr_search_improves=[0,0,0,0,0]
def assign_CFLPr1(maxr2,maxr,mincp): # improve coverage or distance
	global node_groups
	global cflpr_search_time
	t=time.time()
	ulist = []
	for i in range(num_units):
		if nodes[i][3]==0: continue
		k=node_groups[i]
		if nodedij[i][k]>maxr: 
			ulist.append(i)
	if ulist == []: return
	random.shuffle(ulist)
	cover=0
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if nodedij[i][k]>=maxr: break
			if k==node_groups[i]: break
			if nodes[i][3]<=facilityCapacity[k]-district_info[k][1]:
				node_groups[i]=k
				update_cflpr_district_info()
				cover+=nodes[i][3]
				cflpr_search_improves[0]+=1
				break
	#print "cover more:", cover,
	cflpr_search_time[0]+=time.time()-t

def assign_CFLPr2(maxr2,maxr,mincp): #min overload
	global node_groups
	global cflpr_search_time
	if objective_overload<=0: return
	t=time.time()
	ulist = []
	overload=objective_overload
	reduced=0
	for k in range(num_districts):
		if centersID[k]<0: continue
		if district_info[k][4]<=0.1: continue
		klist=[ [x,nodedij[x][k]] for x in range(num_units) if node_groups[x]==k]
		klist.sort(key=lambda x: -x[1])
		ulist+=[x[0] for x in klist[:len(klist)/5] ]
	if len(ulist)>=0: 
		random.shuffle(ulist)
		for i in ulist:
			k=node_groups[i]
			if district_info[k][4]<=0: continue
			for k in NearFacilityList[i]:
				if centersID[k]<0: continue
				if nodedij[i][k]>maxr: break
				if nodes[i][3]<=facilityCapacity[k]-district_info[k][1]:
					node_groups[i]=k
					update_cflpr_district_info()
					reduced+=nodes[i][3]
					cflpr_search_improves[1]+=1
					break
	#print "ovld less:",overload-objective_overload,
	cflpr_search_time[1]+=time.time()-t

def assign_CFLPr3(maxr2,maxr,mincp): #min distance
	global node_groups
	global cflpr_search_time
	t=time.time()
	ulist = []
	for i in range(num_units):
		k=node_groups[i]
		if nodes[i][3]==0: continue
		if nodedij[i][k] > maxr: #district_info[k][2]/district_info[k][1]: 
			ulist.append(i)
	if ulist == []: return
	random.shuffle(ulist)
	dis_total=0.0
	for i in ulist:
		k=node_groups[i]
		dis=nodedij[i][k]
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if nodedij[i][k]>=dis: break
			if k==node_groups[i]: break
			if nodes[i][3]<=facilityCapacity[k]-district_info[k][1]:
				node_groups[i]=k
				update_cflpr_district_info()
				dis_total+=(dis-nodedij[i][k])*nodes[i][3]
				cflpr_search_improves[2]+=1
				break
	#print "dist less:", dis_total,
	cflpr_search_time[2]+=time.time()-t

def update_zero_demand():
	global node_groups
	for i in range(num_units):
		if nodes[i][3]>0: continue
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break

def r_r_cflpr(strength):
	global district_info
	ulist=range(num_units)
	random.shuffle(ulist)
	ulist=ulist[:int(strength*num_units)]
	for x in ulist: node_groups[x]=-1
	update_district_info()
	random.shuffle(ulist)
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if nodes[i][3]+district_info[k][1]<=facilityCapacity[k]:
				node_groups[i]=k
				district_info[k][1]+=nodes[i][3]
				break
	for i in ulist:
		if node_groups[i]>=0: continue
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			break

def cmdelp_ils(max_radius,radius_preference,cover_pecentage,multi_start,maxloops): #testing
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global best_centersID_global
	global best_solution_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	global facilityCost
	#global node_neighbors
	global region_pool
	global pool_index
	global is_spp_modeling
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	global penalty_on_demand
	global envy_service_objective
	global travel_distance_weight
	temp_envy_service_objective=-1
	temp_travel_distance_weight=-1
	initialize_instance()
	max_loops_solution_not_improved=maxloops
	multi_start_count=multi_start
	print "num_facility:",max_num_facility
	covered_demand_nodes=[]
	opt_radius=[0.0 for x in range(num_districts)]
	cflp_max_service_radius=max_radius
	cflp_service_radius_preference=radius_preference
	cflp_min_service_coverage_percentage=cover_pecentage
	#penalty_on_demand=10000*sum(facilityCost)/sum(facilityCapacity)
	#penalty_on_demand=current_penalty()
	#if fixed_cost_obj==0.0: 
	#   penalty_on_demand=10000.0
	#print penalty_on_demand,envy_service_distance
	#if envy_service_objective==1: penalty_on_demand*=envy_service_distance
	#if envy_service_objective==2: penalty_on_demand*=envy_service_distance
	#if envy_service_objective==4: penalty_on_demand*=envy_service_distance
	print "penalty_on_demand:",penalty_on_demand
	temp_envy_service_objective=envy_service_objective
	temp_travel_distance_weight=travel_distance_weight
	if envy_service_objective>=1:    
		envy_service_objective=0
		travel_distance_weight=1
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	not_improved_global=0
	init_methods=[0,1]
	#if adaptive_number_of_facilities==0: init_methods=[1,2]
	loops=max(1,multi_start_count)
	if initial_solution_method==9:
		CFLP_LR_main(100)
		update_district_info()
		#penalty_on_demand=10000*objective/total_pop
		best_biobjective_global = MAXNUMBER
		for idx in range (len(all_solutions)):
			node_groups=all_solutions[idx][2][:]
			centersID=all_solutions[idx][1][:]
			update_cflpr_district_info()
			if spatial_contiguity==1:
				repair_fragmented_solution()
			update_cflpr_district_info()
			update_best_solution()
		all_solutions[idx][0]=biobjective
		population=copy.deepcopy(all_solutions)

	for idx in range(loops):
		init_t=time.time()
		drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		update_district_info()
		#if objective/total_pop>1.0:
			#penalty_on_demand=10000*objective/total_pop
			#print "new penalty_on_demand:",penalty_on_demand
		update_cflpr_district_info()
		VND_local_search()
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_cflpr_district_info()
		#for x in district_info:
		#   if x[0]>0: print x 
		coverdemand=0
		coverdemand2=0
		#update_centers()
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		#penalty_demand=objective_overload+coverdemand2+max(total_pop*cover_pecentage/100-coverdemand,0)
		#penalty=100*sum(facilityCost)/sum(facilityCapacity)
		penalty=penalty_on_demand
		update_cflpr_district_info()

		nf=sum(1 for x in centersID if x>=0)
		update_region_pool_all()
		update_best_solution()
		location_check(0)
		print "init. sol.",idx, "mthd",nf,biobjective,objective,objective_overload,coverdemand2, int(cp*100)/100.0,time.time()-t
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		sol=print_equality_measures()
		#print [x for x in centersID if x>=0]
		#if len(population)>=multi_start_count: break

	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	print "pop size",len(population),"pop objs: "+str(population[0][0])+"-"+str(population[-1][0])
	loop=-1
	#penalty_on_demand=10000.0*max(1,objective/total_pop)
	#print "new penalty_on_demand:",penalty_on_demand
	
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))* pow(r,1.2)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_cflpr_district_info()
		bnf=sum(1 for x in centersID if x>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(objective_overload)+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		if random.random()>0.2:        
			dlist,clist=select_region(-1)
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
			loop2=0            
			while 1:
				sta, cids, sol=K_means_uflp(ulist,dlist)
				loop2+=1
				if loop2>10 or sta==1:  
					for x in dlist: centersID[x]=-1
					for x in cids: centersID[x]=x
					for idx in range(len(ulist)):
						i=ulist[idx]
						node_groups[i]=sol[idx]
					break
		else:
			pmp_Whitaker()
		update_cflpr_district_info()
		#o0=biobjective
		location_check(0)
		VND_local_search()
		update_cflpr_district_info()
		#print o0-biobjective,
		update_best_solution()
		update_region_pool_all()
		location_check(1)
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])

		'''sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,50,0.000000001) #bug
		update_cflpr_district_info()
		location_check(2)
		update_best_solution()
		update_region_pool_all()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
'''

		if spatial_contiguity==1:
			repair_fragmented_solution()
			update_cflpr_district_info()
		update_best_solution()
		update_region_pool_all()

		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		all_solutions=copy.deepcopy(population)

		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
		s=str(sidx)+" " 
		if best_biobjective_global<obj-0.000001:  #0.1%
			s+="*"
			impp=(best_biobjective_global-obj)/best_biobjective_global*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: 
			s+="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop) + " Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_fcost))+" "+str(int(objective_overload))
		s+=" Info: " +str(len(population))+" " + str(not_improved_global)+ " "+str(int(time.time()-t))
		coverdemand=0
		coverdemand2=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		#penalty_demand=objective_overload+coverdemand2+max(total_pop*cover_pecentage/100-coverdemand,0)
		s+=" "+str(int(objective_overload)) + " "+  str(coverdemand2) +" "+ str(max(total_pop*cover_pecentage/100-coverdemand,0)) +" "+ str(int(cp*10000)/100.0)
		s+=" "+str(int(biobjective-obj_old)) #+" "+str(population[0][0])+"-"+str(population[-1][0])
		#s+=str(cflpr_search_time)

		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		if time.time()-t > heuristic_time_limit:     break        
		if temp_envy_service_objective>0 and envy_service_objective==0:
			if not_improved_global>=5 or not_improved_global>=max(5, max_loops_solution_not_improved/5) or time.time()-t > heuristic_time_limit/5.0: 
				not_improved_global=0
				envy_service_objective=temp_envy_service_objective
				temp_envy_service_objective=0
				travel_distance_weight=temp_travel_distance_weight
				best_biobjective_global=MAXNUMBER
				for idx in range(len(population)):
					node_groups=population[idx][2][:]
					centersID=population[idx][1][:]
					update_cflpr_district_info()
					if spatial_contiguity==1:
						repair_fragmented_solution()
					update_cflpr_district_info()
					update_best_solution()
					population[idx][0]=biobjective
				population.sort(key=lambda x:x[0])
				all_solutions=copy.deepcopy(population)
				print ("--------------second stage--------------------------")
		if stop_searching==1: break
			   
	#post procedure
	ga_time=time.time()-t
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	print "Heuristic solution:",nf,biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sta=cflpr_scp_model(max_radius,radius_preference,cover_pecentage,ga_time/10,0.00000001)
		if sta>0:
			update_cflpr_district_info()
			update_best_solution()
			nf=sum(1 for x in centersID if x>=0)
			print "spp solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,time.time()-t_spp
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
	#penalty_on_demand=max(facilityCost)
	for idx in range(len(population)):
		node_groups=population[idx][2][:]
		centersID=population[idx][1][:]
		update_cflpr_district_info()
		population[idx][0]=biobjective
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	node_groups=population[0][2][:]
	centersID=population[0][1][:]
	update_cflpr_district_info()
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
	nf=sum(1 for x in centersID if x>=0)
	print "final solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,int(coverdemand*10000/total_pop)/100.0
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]


def cmdelp_matheuristic(max_radius,radius_preference,cover_pecentage,multi_start,maxloops):
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global best_centersID_global
	global best_solution_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	global facilityCost
	#global node_neighbors
	global region_pool
	global pool_index
	global is_spp_modeling
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	global penalty_on_demand
	global envy_service_objective
	global travel_distance_weight
	global envy_objective_weight_of_travelcost
	temp_envy_service_objective=-1
	temp_travel_distance_weight=-1
	initialize_instance()
	for i in range (num_units):
		for j in range (num_districts):
			if nodedij[i][j]> max_radius:
				nodedij[i][j]+=penalty_on_demand
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	if num_units*num_districts<=large_neigborhood_maxIJ:
		if adaptive_number_of_facilities==0: 
			return cpmp_mip_model(max_num_facility,0.0001,0,solver_time_limit,0.000000000001)
		if adaptive_number_of_facilities==1: 
			#SSCFLP_SSCKFLP_model(max_num_facility,r,maxtime,mipgap)
			return cflpr_model(max_radius,radius_preference,cover_pecentage,max_num_facility,solver_time_limit,0.000000001)
	
	max_loops_solution_not_improved=maxloops
	multi_start_count=multi_start
	print "num_facility:",max_num_facility
	covered_demand_nodes=[]
	opt_radius=[0.0 for x in range(num_districts)]
	cflp_max_service_radius=max_radius
	cflp_service_radius_preference=radius_preference
	cflp_min_service_coverage_percentage=cover_pecentage
	temp_envy_service_objective=envy_service_objective
	temp_travel_distance_weight=travel_distance_weight
	if envy_service_objective>=1:    
		envy_service_objective=0
		travel_distance_weight=1
		envy_objective_weight_of_travelcost=1
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]

	init_methods=[0,1,8,9]
	#if adaptive_number_of_facilities==0: init_methods=[1,2]
	loops=max(1,multi_start_count)
	init_methods=[0,1,7,8]
	loops=multi_start_count
	if initial_solution_method==9:
		if adaptive_number_of_facilities==1:
			CFLP_LR_main(100)
		if adaptive_number_of_facilities==0:
			CPMP_LR_main(100)
		penalty=penalty_on_demand
		best_biobjective_global = MAXNUMBER
		for idx in range (len(all_solutions)):
			if adaptive_number_of_facilities==0:
				clist=[x for x in range(num_districts) if centersID[x]>=0]
				if len(clist)>max_num_facility:
					random.shuffle(clist)
					clist=clist[max_num_facility:]
				if len(clist)<max_num_facility:
					clist=[x for x in range(num_districts) if centersID[x]<0]
					random.shuffle(clist)
					clist=clist[:max_num_facility-len(clist)]
					for x in clist: centersID[x]=facilityCandidate[x]
			node_groups=all_solutions[idx][2][:]
			centersID=all_solutions[idx][1][:]
			update_cflpr_district_info()
			if spatial_contiguity==1:
				repair_fragmented_solution()
			VND_local_search()
			all_solutions[idx][2]=node_groups[:]
			all_solutions[idx][1]=centersID[:]
			update_cflpr_district_info()
			update_best_solution()
			all_solutions[idx][0]=biobjective
		for idx in range(max(multi_start_count,len(all_solutions))):
			print "sol.", idx, all_solutions[idx][0],all_solutions[idx][3],all_solutions[idx][4],all_solutions[idx][5]     
		print "inclusion",inclusion
		print "exclusion",exclusion
		population=copy.deepcopy(all_solutions)

	for idx in range(loops):
		if initial_solution_method==9: 
			break
		init_t=time.time()
		sta=0
		if initial_solution_method<0:
			nm=len(init_methods)
			method=init_methods[idx%nm]
		else:
			method=initial_solution_method
		if method==0: #cflp
			drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		if method==1: #DC-cflp
			sta=clscp_mip_model_init(max_radius,radius_preference,cover_pecentage,100,0.01)
			update_zero_demand()
		if method==7: #reduced model
			CPMP_reduced_model(max_num_facility,1,min(1000,num_units*0.5),0.03)
			sta=1
		if method==8: #linear relax model
			tl=max(100,num_units/2)
			if envy_service_objective>=0:
				if adaptive_number_of_facilities==0:
					nf=max_num_facility
				else:
					nf=max_facility_cost*num_districts/sum(facilityCost)
					tl=min(tl,10*nf)
			nu=num_units/nf
			h=1.0
			if nu>40: h=1.5
			if nu>60: h=2.0
			if nu>80: h=2.5
			tl*=h
			solver_message_tmp=solver_message
			sta=cflpr_lp_model(max_radius,radius_preference,cover_pecentage,max_num_facility,tl,0.02)
			solver_message=solver_message_tmp
		if sta<1: 
			method=0
			sta=drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		update_cflpr_district_info()
		if spatial_contiguity==1:
			repair_fragmented_solution()
		VND_local_search()
		update_cflpr_district_info()
		coverdemand=0
		coverdemand2=0
		#update_centers()
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		penalty=penalty_on_demand
		update_cflpr_district_info()
		nf=sum(1 for x in centersID if x>=0)
		update_region_pool_all()
		update_best_solution()
		print "init. sol.",idx, "mthd",method,nf,biobjective,objective,objective_overload,coverdemand2, int(cp*100)/100.0,time.time()-t

		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		sol=print_equality_measures()
		if len(population)>=multi_start_count: break
		if method>=7: break
						
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	print "pop size",len(population),"pop objs: "+str(population[0][0])+"-"+str(population[-1][0])
	loop=-1
	not_improved_global=0
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))* pow(r,1.2)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_cflpr_district_info()
		bnf=sum(1 for x in centersID if x>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(objective_overload)+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		sta=sscflpr_sub_model(max_radius,radius_preference,cover_pecentage,max(50,large_neigborhood_maxIJ/100),1.0e-10)
		update_cflpr_district_info()
		#print [int(obj_old-biobjective)],
		#population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		if obj_old>biobjective*1.00001:
			VND_local_search()
			obj1=biobjective
			#sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,50,0.000000001) #bug
			update_cflpr_district_info()
			location_check(2)
			update_region_pool_all()
			#population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])'''
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_cflpr_district_info()
		VND_local_search()
		update_best_solution()
		update_region_pool_all()

		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		all_solutions=copy.deepcopy(population)

		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
		s=str(sidx)+" " 
		if best_biobjective_global<obj-0.000001:  #0.1%
			s+="*"
			impp=(best_biobjective_global-obj)/best_biobjective_global*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: 
			s+="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop)+ " " +str(sta) + " Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_covered))
		s+=" Info: " +str(len(population))+" " + str(not_improved_global)+ " "+str(int(time.time()-t))
		coverdemand=0
		coverdemand2=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		#penalty_demand=objective_overload+coverdemand2+max(total_pop*cover_pecentage/100-coverdemand,0)
		s+=" "+str(int(objective_overload)) + " "+  str(coverdemand2) +" "+ str(max(total_pop*cover_pecentage/100-coverdemand,0)) +" "+ str(int(cp*10000)/100.0)
		s+=" "+str(int(biobjective-obj_old)) #+" "+str(population[0][0])+"-"+str(population[-1][0])
		#s+=str(cflpr_search_time)

		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		if time.time()-t > heuristic_time_limit:     break        
		if temp_envy_service_objective>0 and envy_service_objective==0:
			if not_improved_global>=5 or not_improved_global>=max(5, max_loops_solution_not_improved/5) or time.time()-t > heuristic_time_limit/5.0: 
				not_improved_global=0
				envy_service_objective=temp_envy_service_objective
				#temp_envy_service_objective=0
				travel_distance_weight=temp_travel_distance_weight
				envy_objective_weight_of_travelcost=travel_distance_weight
				best_biobjective_global=MAXNUMBER
				for idx in range(len(population)):
					node_groups=population[idx][2][:]
					centersID=population[idx][1][:]
					update_cflpr_district_info()
					if spatial_contiguity==1:
						repair_fragmented_solution()
					update_cflpr_district_info()
					update_best_solution()
					population[idx][0]=biobjective
				population.sort(key=lambda x:x[0])
				all_solutions=copy.deepcopy(population)
				print ("--------------second stage--------------------------")
	#post procedure
	ga_time=time.time()-t
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	print "Heuristic solution:",nf,biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sta=cflpr_scp_model(max_radius,radius_preference,cover_pecentage,ga_time/10,0.00000001)
		if sta>0:
			update_cflpr_district_info()
			update_best_solution()
			nf=sum(1 for x in centersID if x>=0)
			print "spp solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,time.time()-t_spp
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
	#penalty_on_demand=max(facilityCost)
	for idx in range(len(population)):
		node_groups=population[idx][2][:]
		centersID=population[idx][1][:]
		update_cflpr_district_info()
		population[idx][0]=biobjective
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	node_groups=population[0][2][:]
	centersID=population[0][1][:]
	for i in range (num_units):
		for j in range (num_districts):
			if nodedij[i][j]> max_radius:
				nodedij[i][j]+=penalty_on_demand
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	for i in range (num_units):
		for j in range (num_districts):
			nodedij[i][j]=nodedij[i][j]%penalty_on_demand
			nodedik[i][j]=nodes[i][3]*nodedij[i][j]

	update_cflpr_district_info()
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
	nf=sum(1 for x in centersID if x>=0)
	print "final solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,int(coverdemand*10000/total_pop)/100.0
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]
			
##LBc << LBr, constrained by radius, using SCLP to generate solutions.
##LBc >> LBr, constrained by capacity, using cSCLP to generate solutions.
##LBc == LBr, constrained by both radius and capacity? using cSCLP to generate solutions? drop???
##LBc << LBr, constrained by radius, using SCLP to generate solutions.
##LBc >> LBr, constrained by capacity, using cSCLP to generate solutions.
##LBc == LBr, constrained by both radius and capacity? using cSCLP to generate solutions? drop???
def cflpr_matheuristic(max_radius,radius_preference,cover_pecentage,multi_start,maxloops):
	global best_biobjective_global
	global node_groups
	global centersID
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	global travel_distance_weight
	if len(all_solutions)==0:
		initialize_instance()
	for i in range (num_units):
		for j in range (num_districts):
			if nodedij[i][j]> max_radius:
				nodedij[i][j]+=penalty_on_demand
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	if num_units*num_districts<=large_neigborhood_maxIJ:
		if adaptive_number_of_facilities==0: 
			cpmp_mip_model(max_num_facility,radius_preference,cover_pecentage,solver_time_limit,0.000000000001)
		if adaptive_number_of_facilities==1: 
			#SSCFLP_SSCKFLP_model(max_num_facility,r,maxtime,mipgap)
			cflpr_model(max_radius,radius_preference,cover_pecentage,max_num_facility,solver_time_limit,0.000000001)
		return            
	max_loops_solution_not_improved=maxloops
	multi_start_count=multi_start
	print "num_facility:",max_num_facility
	covered_demand_nodes=[]
	opt_radius=[0.0 for x in range(num_districts)]
	cflp_max_service_radius=max_radius
	cflp_service_radius_preference=radius_preference
	cflp_min_service_coverage_percentage=cover_pecentage
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	'''if max_num_facility>0 and max_num_facility<=10:
		if 2 in sub_model_neigborhood_types: sub_model_neigborhood_types.remove(2)
		if 3 in sub_model_neigborhood_types: sub_model_neigborhood_types.remove(3)'''
	not_improved_global=0
	loops=multi_start_count
	if initial_solution_method==9:# and len(all_solutions)>=1:
		if adaptive_number_of_facilities==1:
			CFLP_LR_main(100)
		#CKFLP_LR_main(200）
		#CFLP_LR_main(100)
		if adaptive_number_of_facilities==0:
			CPMP_LR_main(100)
		#penalty=current_penalty()
		#if penalty_on_demand==0.0:
		#   update_district_info()
		#   penalty_on_demand=10000*objective/total_pop
		penalty=penalty_on_demand
		best_biobjective_global = MAXNUMBER
		for idx in range (len(all_solutions)):
			if adaptive_number_of_facilities==0:
				clist=[x for x in range(num_districts) if centersID[x]>=0]
				if len(clist)>max_num_facility:
					random.shuffle(clist)
					clist=clist[max_num_facility:]
				if len(clist)<max_num_facility:
					clist=[x for x in range(num_districts) if centersID[x]<0]
					random.shuffle(clist)
					clist=clist[:max_num_facility-len(clist)]
					for x in clist: centersID[x]=facilityCandidate[x]
			node_groups=all_solutions[idx][2][:]
			centersID=all_solutions[idx][1][:]
			update_cflpr_district_info()
			if spatial_contiguity==1:
				repair_fragmented_solution()
				VND_local_search()
			all_solutions[idx][2]=node_groups[:]
			all_solutions[idx][1]=centersID[:]
			update_cflpr_district_info()
			update_best_solution()
			all_solutions[idx][0]=biobjective
		for idx in range(max(multi_start_count,len(all_solutions))):
			print "sol.", idx, all_solutions[idx][0],all_solutions[idx][3],all_solutions[idx][4],all_solutions[idx][5]     
		print "inclusion",inclusion
		print "exclusion",exclusion
		population=copy.deepcopy(all_solutions)
		if initial_solution_method==-1:
			population=copy.deepcopy(all_solutions[:max(3,multi_start_count/2)])

	for idx in range(loops):
		if initial_solution_method==9: 
			break
		if len(all_solutions)>=1:            
			break
		init_t=time.time()
		sta=0
		if initial_solution_method<0:
			nm=len(init_methods)
			method=init_methods[idx%nm]
			#method=idx%5
		else:
			method=initial_solution_method
		if method==0: #cflp
			drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		if method==1: #DC-cflp
			sta=clscp_mip_model_init(max_radius,radius_preference,cover_pecentage,100,0.01)
			update_zero_demand()
		if method==7: #reduced model
			tl=max(100,num_units/2)
			if adaptive_number_of_facilities==0:
				nf=max_num_facility
			else:
				nf=max_facility_cost*num_districts/sum(facilityCost)
			tl=min(tl,nf*math.log(num_units)*math.log(num_districts))
			tl=min(tl,nf*10)
			nu=num_units/nf
			h=1.0
			if nu>40: h=1.5
			if nu>60: h=2.0
			if nu>80: h=2.5
			tl*=h
			solver_message_tmp=solver_message
			solver_message=1
			sta=CPMP_reduced_model(max_num_facility,1,tl,0.03)
			solver_message=solver_message_tmp
		if method==8: #linear relax model
			tl=max(100,num_units/2)
			if adaptive_number_of_facilities==0:
				nf=max_num_facility
			else:
				nf=max_facility_cost*num_districts/sum(facilityCost)
			tl=min(tl,nf*math.log(num_units)*math.log(num_districts))
			tl=min(tl,200)
			nu=80
			if nf>0: nu=num_units/nf
			h=1.0
			if nu>40: h=1.5
			if nu>60: h=2.0
			if nu>80: h=2.5
			tl*=h
			solver_message_tmp=solver_message
			solver_message=1
			sta=cflpr_lp_model(max_radius,radius_preference,cover_pecentage,max_num_facility,tl,0.02)
			solver_message=solver_message_tmp
		if sta<1: 
			method=0
			sta=drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		update_cflpr_district_info()
		sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,10,0.000000001) 
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_cap_centers()            
		VND_local_search()    
		update_cflpr_district_info()
		coverdemand=0
		coverdemand2=0
		#update_centers()
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		penalty=penalty_on_demand
		update_cflpr_district_info()
		if envy_service_objective==1 or envy_service_objective==2:
			for i in range(int(num_units*max_num_facility/10000)):
				sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,10,0.000000001) 
				update_cflpr_district_info()
		nf=sum(1 for x in centersID if x>=0)
		update_region_pool_all()
		update_best_solution()
		location_check(1)
		print "init. sol.",idx, "mthd",method,nf,biobjective,objective,objective_overload,coverdemand2, int(cp*100)/100.0,time.time()-t
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		sol=print_equality_measures()
		#print [x for x in centersID if x>=0]
		if len(population)>=multi_start_count: break
		if method>=7: break
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	print "pop size",len(population),"obj values: "+str(population[0][0])+"-"+str(population[-1][0])
	loop=-1
	
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))*pow(r,1.5)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_cflpr_district_info()
		bnf=sum(1 for x in centersID if x>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(objective_overload)+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		sta=sscflpr_sub_model(max_radius,radius_preference,cover_pecentage,max(50,large_neigborhood_maxIJ/100),1.0e-10)
		location_check(1)
		update_cflpr_district_info()
		VND_local_search()
		location_check(2)
		'''if obj_old>biobjective*1.0000001:
			sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,10,0.000000001) 
			update_cflpr_district_info()
			location_check(3)'''
		if spatial_contiguity==1: 
			repair_fragmented_solution()
			location_check(4)
			VND_local_search()
		update_cflpr_district_info()
		location_check(5)
		update_best_solution()
		update_region_pool_all()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])

		'''update_cap_centers()            
		VND_local_search()
		update_cflpr_district_info()
		update_best_solution()
		update_region_pool_all()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])'''
		
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		all_solutions=copy.deepcopy(population)
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
		s="" 
		if best_biobjective_global<obj-0.000001: 
			s+="*"
			#impp=(best_biobjective_global-obj)/(best_biobjective_global-best_objective_fcost_global)*1000 #-0.1%
			impp=(best_biobjective_global-obj)/best_biobjective_global*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: 
			s+="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop) + " " +str(sta)+" Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_overload))
		s+=" Info: " +str(len(population))+" " + str(not_improved_global)+ " "+str(int(time.time()-t))
		coverdemand=0
		coverdemand2=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		#penalty_demand=objective_overload+coverdemand2+max(total_pop*cover_pecentage/100-coverdemand,0)
		s+=" "+str(int(objective_overload)) + " "+  str(coverdemand2) +" "+ str(max(total_pop*cover_pecentage/100-coverdemand,0)) +" "+ str(int(cp*10000)/100.0)
		s+=" "+str(int(biobjective-obj_old)) #+" "+str(population[0][0])+"-"+str(population[-1][0])
		arcpy_print(s)
		#print not_improved_global, max_loops_solution_not_improved
		if not_improved_global >= max_loops_solution_not_improved: break
		if stop_searching==1: break
		if time.time()-t>heuristic_time_limit: break
		'''if not_improved_global >=min(10, max(5, multi_start_count, max_loops_solution_not_improved/10) ) and temp_envy_service_objective>0 and temp_envy_service_objective!=envy_service_objective: 
			if envy_service_objective!=temp_envy_service_objective:
				print ("--------------second stage--------------------------")
			not_improved_global=0
			envy_service_objective=temp_envy_service_objective
			temp_envy_service_objective=0
			travel_distance_weight=temp_travel_distance_weight
			best_biobjective_global=MAXNUMBER
			for idx in range(len(population)):
				node_groups=population[idx][2][:]
				centersID=population[idx][1][:]
				update_cflpr_district_info()
				if spatial_contiguity==1:
					repair_fragmented_solution()
				update_cflpr_district_info()
				update_best_solution()
				population[idx][0]=biobjective
			population.sort(key=lambda x:x[0])
			population=population[:max(5,multi_start_count)]
			all_solutions=copy.deepcopy(population)'''
	#post procedure
	ga_time=time.time()-t
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	print "Heuristic solution:",nf,biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sta=cflpr_scp_model(max_radius,radius_preference,cover_pecentage,ga_time/10,0.00000001)
		if sta>0:
			update_cflpr_district_info()
			update_best_solution()
			nf=sum(1 for x in centersID if x>=0)
			print "spp solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,time.time()-t_spp
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
	#penalty_on_demand=max(facilityCost)
	for idx in range(len(population)):
		node_groups=population[idx][2][:]
		centersID=population[idx][1][:]
		update_cflpr_district_info()
		population[idx][0]=biobjective
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	node_groups=population[0][2][:]
	centersID=population[0][1][:]
	for i in range (num_units):
		for j in range (num_districts):
			nodedij[i][j]=nodedij[i][j]%penalty_on_demand
			nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	update_cflpr_district_info()
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
	nf=sum(1 for x in centersID if x>=0)
	print "final solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,int(coverdemand*10000/total_pop)/100.0
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

#DCCFLP canbe solve by cflpr_HM
def dccflp_matheuristic(max_radius,radius_preference,cover_pecentage,multi_start,maxloops):
	global node_groups
	global centersID
	global best_biobjective_global
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	initialize_instance()
	for i in range (num_units):
		for j in range (num_districts):
			if nodedij[i][j]> max_radius:
				nodedij[i][j]+=penalty_on_demand
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	if num_units*num_districts<=large_neigborhood_maxIJ:
		if adaptive_number_of_facilities==0: 
			return cpmp_mip_model(max_num_facility,0.0001,0,solver_time_limit,0.000000000001)
		if adaptive_number_of_facilities==1: 
			#SSCFLP_SSCKFLP_model(max_num_facility,r,maxtime,mipgap)
			return cflpr_model(max_radius,radius_preference,cover_pecentage,max_num_facility,solver_time_limit,0.000000001)
	max_loops_solution_not_improved=maxloops
	multi_start_count=multi_start
	print "num_facility:",max_num_facility
	covered_demand_nodes=[]
	opt_radius=[0.0 for x in range(num_districts)]
	cflp_max_service_radius=max_radius
	cflp_service_radius_preference=radius_preference
	cflp_min_service_coverage_percentage=cover_pecentage
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	'''if max_num_facility>0 and max_num_facility<=10:
		if 2 in sub_model_neigborhood_types: sub_model_neigborhood_types.remove(2)
		if 3 in sub_model_neigborhood_types: sub_model_neigborhood_types.remove(3)'''
	not_improved_global=0
	loops=multi_start_count
	if initial_solution_method==9 or initial_solution_method==9:
		CFLP_LR_main(100)
		penalty=penalty_on_demand
		best_biobjective_global = MAXNUMBER
		for idx in range (len(all_solutions)):
			if adaptive_number_of_facilities==0:
				clist=[x for x in range(num_districts) if centersID[x]>=0]
				if len(clist)>max_num_facility:
					random.shuffle(clist)
					clist=clist[max_num_facility:]
				if len(clist)<max_num_facility:
					clist=[x for x in range(num_districts) if centersID[x]<0]
					random.shuffle(clist)
					clist=clist[:max_num_facility-len(clist)]
					for x in clist: centersID[x]=facilityCandidate[x]
			node_groups=all_solutions[idx][2][:]
			centersID=all_solutions[idx][1][:]
			update_cflpr_district_info()
			if spatial_contiguity==1:
				repair_fragmented_solution()
				VND_local_search()
			all_solutions[idx][2]=node_groups[:]
			all_solutions[idx][1]=centersID[:]
			update_cflpr_district_info()
			update_best_solution()
			all_solutions[idx][0]=biobjective
		for idx in range(max(multi_start_count,len(all_solutions))):
			print "sol.", idx, all_solutions[idx][0],all_solutions[idx][3],all_solutions[idx][4],all_solutions[idx][5]     
		print "inclusion",inclusion
		print "exclusion",exclusion
		population=copy.deepcopy(all_solutions)
		if initial_solution_method==-1:
			population=copy.deepcopy(all_solutions[:max(3,multi_start_count/2)])

	for idx in range(loops):
		if initial_solution_method==9: 
			break
		init_t=time.time()
		sta=0
		if initial_solution_method<0:
			nm=len(init_methods)
			method=init_methods[idx%nm]
			#method=idx%5
		else:
			method=initial_solution_method
		if method==0: #cflp
			drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		if method==1: #DC-cflp
			sta=clscp_mip_model_init(max_radius,radius_preference,cover_pecentage,100,0.01)
			update_zero_demand()
		if method==7: #reduced model
			CPMP_reduced_model(max_num_facility,1,min(1000,num_units*0.5),0.03)
			sta=1
		if method==8: #linear relax model
			tl=max(100,num_units/5)
			solver_message_tmp=solver_message
			sta=cflpr_lp_model(max_radius,radius_preference,cover_pecentage,max_num_facility,tl,0.02)
			solver_message=solver_message_tmp
		if sta<1: 
			method=0
			sta=drop_method_cflpr(max_radius,radius_preference,cover_pecentage)
		update_cflpr_district_info()
		sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,10,0.000000001) 
		if spatial_contiguity==1:
			repair_fragmented_solution()
		#update_cap_centers()            
		VND_local_search()    
		update_cflpr_district_info()
		coverdemand=0
		coverdemand2=0
		#update_centers()
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		penalty=penalty_on_demand
		update_cflpr_district_info()
		nf=sum(1 for x in centersID if x>=0)
		update_region_pool_all()
		update_best_solution()
		print "init. sol.",idx, "mthd",method,nf,biobjective,objective,objective_overload,coverdemand2, int(cp*100)/100.0,time.time()-t

		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		sol=print_equality_measures()
		#print [x for x in centersID if x>=0]
		if len(population)>=multi_start_count: break
		if method>=7: break
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	print "pop size",len(population),", pop objs: "+str(population[0][0])+"-"+str(population[-1][0])
	loop=-1
	
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))*pow(r,1.6)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_cflpr_district_info()
		bnf=sum(1 for x in centersID if x>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(objective_overload)+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		sta=sscflpr_sub_model(max_radius,radius_preference,cover_pecentage,max(50,large_neigborhood_maxIJ/100),1.0e-10)
		update_cflpr_district_info()
		'''VND_local_search()
		if obj_old>biobjective*1.0000001:
			sscflpr_sub_assign_model(max_radius,radius_preference,cover_pecentage,10,0.000000001) 
			update_cflpr_district_info()'''
		if spatial_contiguity==1: 
			repair_fragmented_solution()
			VND_local_search()
		update_cflpr_district_info()
		update_best_solution()
		update_region_pool_all()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])

		'''if fixed_cost_obj==0 and cover_pecentage==0:
			update_cap_centers()            
			VND_local_search()
			update_cflpr_district_info()
			update_best_solution()
			update_region_pool_all()'''
		#print int(biobjective),

		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		all_solutions=copy.deepcopy(population)
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
		s=""#str(sidx)+" " 
		if best_biobjective_global<obj-0.000001: 
			s+="*"
			#impp=(best_biobjective_global-obj)/(best_biobjective_global-best_objective_fcost_global)*1000 #-0.1%
			impp=(best_biobjective_global-obj)/best_biobjective_global*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: 
			s+="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop)+ " " +str(sta) + " Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_fcost))
		s+=" Info: " +str(len(population))+" " + str(not_improved_global)+ " "+str(int(time.time()-t))
		coverdemand=0
		coverdemand2=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		#penalty_demand=objective_overload+coverdemand2+max(total_pop*cover_pecentage/100-coverdemand,0)
		s+=" "+str(int(objective_overload)) + " "+  str(coverdemand2) +" "+ str(max(total_pop*cover_pecentage/100-coverdemand,0)) +" "+ str(int(cp*10000)/100.0)
		s+=" "+str(int(biobjective-obj_old)) #+" "+str(population[0][0])+"-"+str(population[-1][0])
		arcpy_print(s)
		#print not_improved_global, max_loops_solution_not_improved
		if not_improved_global >= max_loops_solution_not_improved: break
		if stop_searching==1: break

	ga_time=time.time()-t
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	print "Heuristic solution:",nf,biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sta=cflpr_scp_model(max_radius,radius_preference,cover_pecentage,ga_time/10,1.0e-10)
		if sta>0:
			update_cflpr_district_info()
			update_best_solution()
			nf=sum(1 for x in centersID if x>=0)
			print "spp solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,time.time()-t_spp
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
	#penalty_on_demand=max(facilityCost)
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	for i in range (num_units):
		for j in range (num_districts):
			nodedij[i][j]=nodedij[i][j]%penalty_on_demand
			nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	update_cflpr_district_info()
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
	nf=sum(1 for x in centersID if x>=0)
	print "final solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,int(coverdemand*10000/total_pop)/100.0
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

def uflp_matheuristic(max_radius,radius_preference,cover_pecentage,multi_start,maxloops):
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global best_centersID_global
	global best_solution_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	global facilityCost
	#global node_neighbors
	global region_pool
	global pool_index
	global is_spp_modeling
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	global penalty_on_demand
	initialize_instance()
	max_loops_solution_not_improved=maxloops
	multi_start_count=multi_start
	print "num_facility:",max_num_facility
	covered_demand_nodes=[]
	opt_radius=[0.0 for x in range(num_districts)]
	cflp_max_service_radius=max_radius
	cflp_service_radius_preference=radius_preference
	cflp_min_service_coverage_percentage=cover_pecentage
	#penalty_on_demand=10000.0
	print "penalty_on_demand",penalty_on_demand
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	if sum(facilityCost)<1:
		for x in range(num_districts):
			facilityCost[x]=100000000
	not_improved_global=0
	init_methods=[0,1,2,3,4]#[1,2,4] #SCLP, CSCLP, Drop
	if adaptive_number_of_facilities==0: init_methods=[1,2]
	loops=multi_start_count
	if adaptive_number_of_facilities==0 and initial_solution_method==9: #pmp-ils
		max_loops_solution_not_improved=max(10,multi_start_count*2)
		ils_pmp_envy(max_num_facility,multi_start_count,7200,-1)
		if spatial_contiguity==1: repair_fragmented_solution()
		max_loops_solution_not_improved=maxloops
		population=all_solutions
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		print "----------------matheuristic-----------------"
	if adaptive_number_of_facilities==0 and initial_solution_method!=9: #
		for idx in range(multi_start_count):
			best_biobjective = MAXNUMBER
			ulist=[]
			sample_size=min(num_units,30*max_num_facility)
			while len(ulist)<sample_size: 
				u=random.randint(0,num_units-1)
				if u not in ulist: ulist.append(u)
			random.shuffle(ulist)
			obj,centers=k_medoids_sampling(ulist,[])
			if len(centers)!=max_num_facility: continue
			centersID=[-1 for x in range(num_units)]
			for x in centers: centersID[x]=facilityCandidate[x]
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					node_groups[i]=k
					break
			nf2=sum(1 for x in centersID if x>=0)
			sta=1
			print "searching ",
			while sta==1:
				print ".",
				sta=pmp_TB()
				update_envy_district_info()
			print ""
			if spatial_contiguity==1: repair_fragmented_solution()
			update_best_solution()
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
			nf=sum(1 for x in centersID if x>=0)
			print "init solution", idx, nf2,nf,biobjective,objective
	if adaptive_number_of_facilities==1 and initial_solution_method==9:
		sol=[]
		for idx in range(multi_start_count):
			uflp_ils(max_radius,radius_preference,cover_pecentage,1,6)
			if spatial_contiguity==1: repair_fragmented_solution()
			sol.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population=sol
		all_solutions=sol
		print "----------------matheuristic-----------------"        
	if adaptive_number_of_facilities==1 and initial_solution_method!=9:
		for idx in range(multi_start_count):
			init_t=time.time()
			if envy_service_objective!=0:
				sta=drop_method_uflp_envy1(max_radius,radius_preference,cover_pecentage)
			if envy_service_objective==2:
				sta=drop_method_uflp_envy2(max_radius,radius_preference,cover_pecentage)
			nf=sum(1 for x in centersID if x>=0)
			#penalty=max(facilityCost)/(total_pop/nf)*100
			#penalty=penalty_on_demand
			#if penalty<penalty_on_demand: penalty_on_demand=penalty
			if spatial_contiguity==1: repair_fragmented_solution()
			update_cflpr_district_info()
			coverdemand=0
			coverdemand2=0
			for i in range(num_units):
				k=node_groups[i]
				if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
				if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
			cp=coverdemand*1.0/total_pop
			nf=sum(1 for x in centersID if x>=0)
			update_region_pool_all()
			update_best_solution()
			location_check(0)
			print "init. sol.",idx, nf,biobjective,objective,objective_overload,coverdemand2, int(cp*100)/100.0,time.time()-t
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
	max_loops_solution_not_improved=maxloops
	population.sort(key=lambda x:x[0])
	all_solutions=population
	loop=-1
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))* pow(r,1.5)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_cflpr_district_info()
		bnf=sum(1 for x in centersID if x>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(objective_overload)+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		MIP_UFLP_location_search()
		if spatial_contiguity==1: repair_fragmented_solution()
		update_cflpr_district_info()
		update_best_solution()
		update_region_pool_all()
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
		s="" 
		if best_biobjective_global<obj-0.000001:  #0.1%
			s="*"
			impp=(best_biobjective_global-obj)/(best_biobjective_global-best_objective_fcost_global)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: s="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop) + " Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_fcost))
		s+=" Info: " +str(not_improved_global)+ " "+str(int(time.time()-t))
		coverdemand=0
		coverdemand2=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
			if nodedij[i][k]>max_radius: coverdemand2+=nodes[i][3]
		cp=coverdemand*1.0/total_pop
		s+=" "+str(int(objective_overload)) + " "+  str(coverdemand2) +" "+ str(max(total_pop*cover_pecentage/100-coverdemand,0)) +" "+ str(int(cp*10000)/100.0)
		s+=" "+str(int(biobjective-obj_old))
		#s+=str(cflpr_search_time)
		arcpy_print(s)
		
		obj=biobjective
		population.append([obj,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		all_solutions=population
		if not_improved_global >= max_loops_solution_not_improved: break
		if time.time()-t_ga > heuristic_time_limit:  break
	#post procedure
	ga_time=time.time()-t
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	print "Heuristic solution:",nf,biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
  
	#penalty_on_demand=max(facilityCost)*10000
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sta=cflpr_scp_model(max_radius,radius_preference,cover_pecentage,min(ga_time/10,200),1.0e-10)
		if sta>0:
			update_cflpr_district_info()
			update_best_solution()
			nf=sum(1 for x in centersID if x>=0)
			print "spp solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,time.time()-t_spp
			population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
		
	for idx in range(len(all_solutions)):
		node_groups=all_solutions[idx][2][:]
		centersID=all_solutions[idx][1][:]
		update_cflpr_district_info()
		all_solutions[idx][0]=obj
	population.sort(key=lambda x:x[0])
	node_groups=population[0][2][:]
	centersID=population[0][1][:]
	update_cflpr_district_info(max_radius,radius_preference,cover_pecentage)
	coverdemand=0
	for i in range(num_units):
		k=node_groups[i]
		if nodedij[i][k]<=radius_preference: coverdemand+=nodes[i][3]
	nf=sum(1 for x in centersID if x>=0)
	print "final solution:",nf,biobjective,objective_fcost,objective,objective_overload,objective/total_pop,int(coverdemand*10000/total_pop)/100.0
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

def uflp_pmp_shuffle():
	strategy=[[3,3],[2,2],[2,2]]
	nf=sum(1 for x in centersID if x>=0)
	#purb_strenth=min(4,nf*5/100)
	#if purb_strenth==4:strategy=[[4,4],[3,3],[2,2]]
	if adaptive_number_of_facilities==1:
		strategy=[[0,1],[1,0],[2,1],[1,2]]
	idx=random.randint(0,len(strategy)-1)
	clist=[x for x in range(num_districts) if centersID[x]<0]
	random.shuffle(clist)
	for x in range(strategy[idx][0]):
		k=clist[x]
		centersID[k]=facilityCandidate[k]
		for i in range(num_units):
			k1=node_groups[i]
			if nodedij[i][k1]>nodedij[i][k]:
				node_groups[x]=k
	clist=[x for x in range(num_districts) if centersID[x]>=0]
	random.shuffle(clist)
	for x in range(strategy[idx][1]):
		k=clist[x]
		centersID[k]=-1
		ulist=[y for y in range(num_units) if node_groups[y]==k]
		for i in ulist:
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break
	#update_cflpr_district_info()

def check_required_facility():
	for x in facility_inclusion_list:
	   if x not in node_groups:
		   print "facility", x,"not used!"

def current_penalty():
	if penalty_on_demand==0.0:#return 10*sum(facilityCost)/sum(facilityCapacity)
		return 100*max(facilityCost)*num_districts/sum(facilityCapacity)
	else:
		return penalty_on_demand
	 

sub_model_tabu_list=[]
def sscflpr_sub_model(max_radius2,max_radius,cover_pecentage,time_limit,mipgap): 
	#if adaptive_number_of_facilities==0 and envy_service_objective>0:
	#   return cpmp_envy_sub_model(max_radius2,max_radius,cover_pecentage,time_limit,mipgap)
	global centersID
	global node_groups
	global time_LNS1
	t=time.time()
	rand=0
	if random.random()>10.5: rand=1
	dlist=[]
	ulist=[]

	neigborhood_index=0
	if len(sub_model_neigborhood_types)==1:
		neigborhood_index=sub_model_neigborhood_types[0]
	if len(sub_model_neigborhood_types)==0:
		neigborhood_index=0
	if len(sub_model_neigborhood_types)>1:       
		idx=random.randint(0,len(sub_model_neigborhood_types)-1)
		neigborhood_index=sub_model_neigborhood_types[idx]
	#0 circle, 1 corridor, 2 large circle, 3 very large
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	r=random.random()
	neig=neigborhood_index
	try_times=0
	while try_times<num_units/2:
		try_times+=1
		if neigborhood_index==0:
			dlist,clist=select_region(-1)
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
		if neigborhood_index==1:
			dlist,clist=select_corridor_region()
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
		if neigborhood_index==2:
			dlist,clist=select_region_adaptive(-1)
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
		if neigborhood_index==3:
			if nf<=30:
				dlist=[x for x in range(num_districts) if centersID[x]>=0]
				ulist=range(num_units)
				clist=[x for x in range(num_districts) if centersID[x]<0 and x not in exclusion]
				random.shuffle(clist)
			else:
				u=random.randint(0,num_units-1)
				dlist=[]
				u=random.randint(0,num_units-1)
				for k in NearFacilityList[u]:
					if centersID[k]>=0:
						dlist.append(k)
					if len(dlist)>=min(30,nf):
						break
				ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
				clist=[x for x in NearFacilityList[u] if centersID[x]<0 and x not in exclusion]
				random.shuffle(clist)
		break
	if spatial_contiguity==1:
		clist=[x for x in clist if facilityCandidate[x] in ulist]
	nfnu=len(dlist)*len(ulist)
	ratio=max(1.0,1.0*large_neigborhood_maxIJ/len(ulist)/len(dlist))    
	ratio=min(ratio, 0.5*len(ulist)/len(dlist)) #num of candadates < len(ulist)/2
	numcl=len(dlist)*ratio   
	'''if neigborhood_index<=1:
		numcl=max(numcl, len(clist)*0.05)'''
	clist=clist[:int(numcl)]
	centers=list(set(clist+dlist))
	exist_facility=[]#[x for x in range(num_districts) if centersID[x]>=0 and x not in centers and facilityCapacity[x]-district_info[x][1]>0]
	#print [neig,len(dlist),len(centers),len(ulist)],
	prob = pulp.LpProblem("cflp_sub",pulp.LpMinimize)
		
	xvariables={}
	costs={}
	penalty=penalty_on_demand
	weight_of_travelcost=travel_distance_weight
	nearest_facilities=num_districts#num_districts*10/nf
	for i in ulist:
		for j in centers+exist_facility:
			#if j not in NearFacilityList[i][:nearest_facilities] and j not in dlist:
			#   continue
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j] *weight_of_travelcost
			if location_problem==9:
				costs["x_" +str(i)+ "_"+ str(j)]= nodedij[i][j] *weight_of_travelcost
			d=nodedij[i][j]
			if d>max_radius2:
				costs["x_" +str(i)+ "_"+ str(j)]+= nodes[i][3]*penalty
			if envy_service_objective==1 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	if cover_pecentage>0:
		zvariable=pulp.LpVariable("z", 0, None, pulp.LpContinuous) #cover gap
	if envy_service_objective==2:
		z3variable=pulp.LpVariable("z3", 0, None, pulp.LpContinuous) #envy gap
	z2variables={}
	z3variables={}
	for i in centers:
		z2variables["z2_" +str(i)]=pulp.LpVariable("z2_" +str(i), 0, None, pulp.LpInteger) #overload
	if facilityMinimumCapacity>0:
		for i in centers:
			z3variables["z3_" +str(i)]=pulp.LpVariable("z3_" +str(i), 0, None, pulp.LpInteger) #lowerload
	if max_facility_cost>0:
		z4variable=pulp.LpVariable("z4", 0, None, pulp.LpContinuous) #above max_cost

	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for x in xvariables:
			obj+=costs[x]*xvariables[x]
	for x in z2variables:
		obj += penalty*z2variables[x]
	if facilityMinimumCapacity>0:
		for x in z3variables:
			obj += penalty*z3variables[x]
	if cover_pecentage>0:
		obj+=penalty*zvariable
	if envy_service_objective==2:
		obj+= penalty*z3variable
	if max_facility_cost>0:
		obj+= penalty*z4variable
	prob += obj

	for i in ulist:
		s=""
		for j in centers+exist_facility:
			#if j not in NearFacilityList[i][:nearest_facilities] and j not in dlist:
			#   continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1

	for k in centers:
		s=""
		for i in ulist:
			#if k not in NearFacilityList[i][:nearest_facilities] and k not in dlist:
			#   continue
			s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
		if facilityMinimumCapacity>0:
			s2 = s + z3variables["z3_" +str(k)]
			s2 -=  facilityMinimumCapacity*yvariables["y_" +str(k)]
			prob += s2 >= 0       
			#prob += s + z3variables["z3_" +str(k)] >= facilityMinimumCapacity*yvariables["y_" +str(k)]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)]
		s-= z2variables["z2_" +str(k)]
		prob += s <= 0

	for k in exist_facility:
		s=""
		for i in ulist:
			#if k not in NearFacilityList[i][:nearest_facilities] and k not in dlist:
			#   continue
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(k)]
		if len(s)>0:
			prob+= s <= facilityCapacity[k] - district_info[k][1]

	for k in centers:
		s= z2variables["z2_" +str(k)]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)]
		prob += s <= 0

	if max_num_reserved_facility>0:
		eflist=[1 for k in facility_inclusion_list if centersID[k]>=0 and k not in dlist]        
		enf=sum(eflist)
		s=""
		for k in centers:
			if k in facility_inclusion_list:
				s+=yvariables["y_" +str(k)]
		prob += s >= min(max_num_reserved_facility,len(facility_inclusion_list))-enf
	if cover_pecentage>0:
		total_cover1=0
		total_cover2=0
		for i in range(num_units):
			if nodedij[i][node_groups[i]]>max_radius: continue
			if i in ulist: 
				total_cover1+=nodes[i][3]
			else: total_cover2+=nodes[i][3]
		min_covered=total_pop*cover_pecentage/100-total_cover2
		s=""
		for i in ulist:
			for j in centers+exist_facility:
				#if j not in NearFacilityList[i][:nearest_facilities] and j not in dlist:
				#   continue
				if nodedij[i][j]>max_radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
		s+=zvariable
		prob += s>=min_covered

	s=""
	for x in yvariables: s+=yvariables[x]
	numf=sum(1 for x in centersID if x>=0)
	if adaptive_number_of_facilities==0:
		if numf==max_num_facility:
			prob += s== len(dlist)
		if numf<max_num_facility:
			prob += s== max_num_facility-numf+len(dlist)
		if numf>max_num_facility:
			prob += s== max_num_facility-numf+len(dlist)
	'''if adaptive_number_of_facilities==1:
		prob += s>= len(dlist)-1
		prob += s<= len(dlist)+1'''

	if max_facility_cost>0:
		efcost=0.0
		for k in range(num_districts):
			if centersID[k]<0: continue
			if k in centers: continue
			efcost+=facilityCost[k]
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		prob += s-z4variable <= max_facility_cost-efcost
		#prob += s <= max_facility_cost-efcost
	if spatial_contiguity==1:
		kilist=[[x,facilityCandidate[x]] for x in centers if facilityCandidate[x] in ulist]
		for k,i in kilist:
			prob += xvariables["x_" +str(i) + "_"+ str(k)] >= yvariables["y_" +str(k)]
	prob.writeLP("_sub_CFLP.lp")
	initvalues=loc_sub_mst(dlist,ulist)
	for x,v in initvalues:
		if x.find("x")==0 and x in xvariables:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	
	if prob.status<=0:
		print "model 'sscflpr_sub_model' unsolved... or infeasible, msg=", prob.status
		prob.writeLP("_sscflpr_sub_model.lp")
		return 0,dlist
	fcost1=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	
	nlist=[]
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	old_centers = centersID[:] #[x for x in range(num_districts) if centersID[x]>=0]
	for x in dlist: centersID[x]=-1
	#for x in ulist: node_groups[x]=-1
	for v in prob.variables():
		if (v.varValue >= 0.9):
			if v.name=="z": continue
			if v.name=="z3": 
				#print v.varValue
				continue
			if v.name=="z4": 
				#print v.varValue
				continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='z2': continue
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
				nlist.append(i)
			if items[0]=='x':
				node_groups[i]=int(items[2])
	time_LNS1+=time.time()-t
	'''obj=biobjective
	update_cflpr_district_info()
	print int(biobjective-obj),  '''  
	return neigborhood_index
def select_can_facility(dlist, clist):
	ulist=[nearCustomer[x] for x in dlist]
	nclist=[[x,0.0] for x in clist]
	for i in range(len(nclist)):
		k=nclist[i][0]
		d=min(nodedij[x][k] for x in ulist)
		nclist[i][1]=d
	nclist.sort(key=lambda x: x[1])
	return [x[0] for x in nclist]

def sscflpr_sub_assign_model(max_radius2,max_radius,cover_pecentage,time_limit,mipgap): 
	global node_groups
	global time_LNS2
	d0=objective
	t=time.time()
	centers=[x for x in range(num_districts) if centersID[x]>=0]
	ulist=[]    
	for i in range(num_units):
		d=nodedij[i][node_groups[i]]
		dlist=[nodedij[i][x] for x in centers]
		dlist.sort()
		if dlist[0]<d or dlist[1]<1.4*dlist[0]:
			ulist.append(i)
			node_groups[i]=-1
	update_district_info()
	prob = pulp.LpProblem("gap",pulp.LpMinimize)
	xvariables={}
	costs={}
	penalty=penalty_on_demand #current_penalty()
	weight_of_travelcost=travel_distance_weight
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j] * weight_of_travelcost
			if nodedij[i][j]>max_radius2:
				costs["x_" +str(i)+ "_"+ str(j)] += nodes[i][3]*penalty
			d=nodedij[i][j]
			if envy_service_objective==1 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	zvariable=pulp.LpVariable("z", 0, None, pulp.LpInteger) #cover gap
	zvariables={}
	z3variables={}
	for j in centers:
		zvariables["z_" + str(j)]=pulp.LpVariable("z_" + str(j), 0, None, pulp.LpInteger) #capa gap
	for i in centers:
		z3variables["z3_" +str(i)]=pulp.LpVariable("z3_" +str(i), 0, None, pulp.LpInteger)
	obj=""
	for i in ulist:
		 for j in centers:
			obj+=costs["x_" +str(i)+ "_"+ str(j)]*xvariables["x_" +str(i)+ "_"+ str(j)]
	for j in centers:
		obj+=penalty*zvariables["z_" + str(j)]
	for j in centers:
		obj+=penalty*z3variables["z3_" + str(j)]
	obj+=penalty*zvariable

	prob += obj
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1
	for k in centers:
		s=""
		for i in ulist:
			s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
		if facilityMinimumCapacity>0:
			prob += s + z3variables["z3_" +str(k)]>= facilityMinimumCapacity - district_info[k][1]
		s-=zvariables["z_" + str(k)]
		prob += s <= facilityCapacity[k]-district_info[k][1]
		#if facilityCapacity[k]<district_info[k][1]: print "&",
	if cover_pecentage>0:
		total_cover1=0
		total_cover2=0
		for i in range(num_units):
			if nodedij[i][node_groups[i]]>max_radius: continue
			if i in ulist: 
				total_cover1+=nodes[i][3]
			else: total_cover2+=nodes[i][3]
		s=""
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>max_radius: continue
				s+=nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(j)]
		s+= zvariable
		min_covered=total_pop*cover_pecentage/100-total_cover2
		prob += s>= min_covered
	'''initvalues=loc_sub_mst(centers,ulist)
	for x,v in initvalues:
		if x.find("x")==0:  xvariables[x].setInitialValue(v)'''
	gap=mipgap
	solver=""
	prob.writeLP("_asgn.lp")    
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap),'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	if prob.status<=0:
		print "model 'sscflpr_sub_assign_model' unsolved... or infeasible, msg=", prob.status
		prob.writeLP("_sscflpr_sub_assign.lp")
		return []
	for v in prob.variables():
		if (v.varValue >= 0.9):
			items=v.name.split('_')
			if items[0]=='x':
				i=int(items[1])
				k=int(items[2])
				if centersID[k]<0: 
					print "assigned to wrong facility",k,v.name,centers
					print [x for x in range(num_districts) if centersID[x]>=0]
				node_groups[i]=k
	time_LNS2+= time.time()-t
	update_district_info()
	'''objective>d0+0.5:
		print objective-d0    
		exit()'''
	location_check(10)

def pmp_model(p,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	prob += obj

	#con 1
	s=""
	for k in centers:
		s+=yvariables["y_" +str(k)]
	prob +=s == p

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1

	for i in ulist:
		for k in centers:
			s= xvariables["x_" +str(i) + "_"+ str(k) ] - yvariables["y_" +str(k)]
			prob +=s <= 0

	#prob.writeLP("_sub_pmp.lp")
	#initvalues=pmp_mst(dlist,ulist)
	#for x,v in initvalues:
	#    if x.find("x")==0:  xvariables[x].setInitialValue(v)
	#    if x.find("y")==0:  yvariables[x].setInitialValue(v)
	#warmStart=True,
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	nlist=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				nlist.append(i)
	centersID=[-1 for x in range(num_districts)]
	for x in nlist: centersID[x]=x
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	return 1

def uflp_sub_model(dlist,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("sub_pmp",pulp.LpMinimize)
	ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	centers=[NearFacilityList[x][0] for x in ulist]
	centers=[x for x in centers if centersID[x]<0]
	centers=list(set(centers))
	random.shuffle(centers)
	centers=centers[:len(dlist)*2]
	centers+=dlist
	centers=list(set(centers))
	existing_facilities=[x for x in range(num_districts) if centersID[x]>=0 and x not in dlist]

	'''maxd=min(nodedij[x][node_groups[x]] for x in range(num_units))
	for i in range(num_units):
		d=min(nodedij[i][x] for x in centers)
		if d <= maxd: #cflp_max_service_radius:
			ulist.append(i)
	ulist=list(set(ulist))'''
	xvariables={}
	costs={}
	nf=sum(1 for x in centersID if x>=0)
	#suppy=total_pop/nf
	penalty=penalty_on_demand 
	#print [len(dlist),len(centers),len(ulist)],
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpContinuous)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
			if nodedij[i][j] > cflp_max_service_radius:
				costs["x_" +str(i)+ "_"+ str(j)] += penalty * nodes[i][3]
			if envy_service_objective==1:
				d=nodedij[i][j]
				if d<= envy_service_distance: continue
				costs["x_" +str(i)+ "_"+ str(j)]+= nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4:
				d=nodedij[i][j]
				if d<= envy_service_distance: continue
				costs["x_" +str(i)+ "_"+ str(j)]+= nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
		for j in existing_facilities:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpContinuous)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]
			if nodedij[i][j] > cflp_max_service_radius:
				costs["x_" +str(i)+ "_"+ str(j)] += penalty * nodes[i][3]
			if envy_service_objective==1:
				d=nodedij[i][j]
				if d<= envy_service_distance: continue
				costs["x_" +str(i)+ "_"+ str(j)]+= nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==4:
				d=nodedij[i][j]
				if d<= envy_service_distance: continue
				costs["x_" +str(i)+ "_"+ str(j)]+= nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
	#zvariables={}
	#for i in ulist:
	#    zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, 1, pulp.LpBinary)
	z1=pulp.LpVariable("z1", 0, None, pulp.LpInteger) #cover gap
	z2=pulp.LpVariable("z2", 0, None, pulp.LpContinuous) #envy gap 
	
	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	for x in yvariables:
		obj += costs[x]*yvariables[x]
	obj+= penalty*z1  + penalty*100*z2
	prob += obj

	#con 1
	if adaptive_number_of_facilities==0:
		s=""
		for k in centers:
			s+=yvariables["y_" +str(k)]
		prob +=s == len(dlist)

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			#if nodedij[i][j] > cflp_max_service_radius: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		for j in existing_facilities:
			#if nodedij[i][j] > cflp_max_service_radius: continue
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1

	for i in ulist:
		for k in centers:
			#if nodedij[i][k] > cflp_max_service_radius: continue
			s= xvariables["x_" +str(i) + "_"+ str(k) ] - yvariables["y_" +str(k)]
			prob +=s <= 0
	#for i in ulist:
	#    s=""
	#    for k in centers:
	#        s += xvariables["x_" +str(i) + "_"+ str(k) ]
	#    prob +=s <= num_units*yvariables["y_" +str(k)]
	covered=0
	for i in range(num_units):
		if i in ulist: continue
		k=node_groups[i]
		d=nodedij[i][k]
		if d<=cflp_service_radius_preference:
			covered+=nodes[i][3]

	s=""
	for i in ulist:
		for j in centers:
			if nodedij[i][j] > cflp_service_radius_preference: continue
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(j)]
		for j in existing_facilities:
			if nodedij[i][j] > cflp_service_radius_preference: continue
			s+=nodes[i][3]*xvariables["x_" +str(i)+ "_"+ str(j)]
	prob +=s +z1 >= total_pop*cflp_min_service_coverage_percentage/100-covered

	prob.writeLP("_uflp.lp")
	initvalues=loc_sub_mst(dlist,ulist)
	for x,v in initvalues:
		if x.find("x")==0:  xvariables[x].setInitialValue(v)
		if x.find("y")==0:  yvariables[x].setInitialValue(v)
	gap=mipgap
	timelmt=5
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,warmStart=True,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True,options=[("MIPGap",gap),("TimeLimit",timelmt)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	for x in dlist: centersID[x]=-1
	for v in prob.variables():
		if (v.varValue >= 0.90):
			if v.name=="z1": continue
			if v.name=="z2": continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2]) 
				node_groups[i]=k
	return 1

TB_tabu_list=[]
def pmp_TB():
	global node_groups
	global centersID
	best_exch=[] #klist,save
	best_obj=biobjective-0.00001
	clist=[x for x in range(num_districts) if centersID[x]>=0]
	random.shuffle(clist)
	klist=[x for x in range(num_districts) if centersID[x]<0]
	random.shuffle(klist)
	for k in clist:
		#u=nearCustomer[k]
		#klist=NearFacilityList[u][num_districts/20:num_districts/5]
		random.shuffle(klist)
		for nk in klist:
			#if nk in clist: continue
			obj=0.0
			new_centersID=centersID[:]
			new_centersID[k]=-1
			new_centersID[nk]=facilityCandidate[nk]
			for i in range(num_units):
				j=node_groups[i]
				if j!=k:
					obj+=min(nodedik[i][j],nodedik[i][nk])
				else:
					for j in NearFacilityList[i]:
						if new_centersID[j]>=0:
							obj+=nodedik[i][j]
							break
			if envy_service_objective==1:
				for i in range(num_units):
					for j in NearFacilityList[i]:
						if new_centersID[j]>=0:
							d=nodedij[i][j]
							if d>envy_service_distance:
								obj+= nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
							break
			if envy_service_objective==4:
				for i in range(num_units):
					for j in NearFacilityList[i]:
						if new_centersID[j]>=0:
							d=nodedij[i][j]
							if d>envy_service_distance:
								obj+= nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
							break
			if obj<best_obj: 
				best_obj=obj
				best_exch.append([k,nk,obj])
				#if num_units==1500: print obj-best_obj,
				#break
			#if len(best_exch)>=1: break
		#if len(best_exch)>=1: break
	if best_exch==[]: 
		#TB_tabu_list.append(centersID[:])
		#print "tabu len=",len(TB_tabu_list)
		return 0
	#print best_exch,best_obj,biobjective
	best_exch.sort(key=lambda x:x[2])
	k=best_exch[0][0]
	centersID[k]=-1
	nk=best_exch[0][1]
	centersID[nk]=facilityCandidate[nk]
	obj=biobjective
	for i in range(num_units):
		j=node_groups[i]
		if j!=k:
			if nodedik[i][j]>nodedik[i][nk]: node_groups[i]=nk
		else:
			for j in NearFacilityList[i]:
				if centersID[j]>=0:
					node_groups[i]=j
					break
	#if centersID not in TB_tabu_list: TB_tabu_list.append(centersID[:])
	update_district_info()
	if spatial_contiguity>=1: repair_fragmented_solution()
	#update_centers()
	#print "tb",obj,biobjective,best_exch
	#if centersID not in TB_tabu_list: TB_tabu_list.append(centersID[:])
	return 1

def pmp_uflp_TB(): #not used in new version
	global node_groups
	global centersID
	best_exch=[] #klist,save
	old_obj=biobjective
	clist=[x for x in range(num_districts) if centersID[x]>=0]
	random.shuffle(clist)
	klist=[x for x in range(num_districts) if centersID[x]<0]
	random.shuffle(klist)
	for k in clist:
		for nk in klist:
			obj=biobjective
			if fixed_cost_obj==1:
				obj+=facilityCost[nk]-facilityCost[k]
			covered=objective_covered
			not_covered=objective_rmax_not_covered
			envy=objective_envy
			new_centersID=centersID[:]
			new_centersID[k]=-1
			new_centersID[nk]=facilityCandidate[nk]
			if max_facility_cost>0:
				fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
				fcost_new = fcost-facilityCost[k]+facilityCost[nk]
				obj-= max(0,fcost-max_facility_cost)*penalty_on_demand
				obj+= max(0,fcost_new-max_facility_cost)*penalty_on_demand
			
			for i in range(num_units):
				ok=node_groups[i]
				if ok!=k:
					if nodedij[i][nk]>=nodedij[i][ok]: continue
					obj+=(nodedik[i][nk]-nodedik[i][ok])*travel_distance_weight
					if nodedij[i][ok]<=cflp_service_radius_preference:
						covered-=nodes[i][3]
					if nodedij[i][nk]<=cflp_service_radius_preference:
						covered+=nodes[i][3]
					if nodedij[i][ok] > cflp_max_service_radius:
						not_covered -= nodes[i][3]
					if nodedij[i][nk] > cflp_max_service_radius:
						not_covered += nodes[i][3]
					if envy_service_objective==1 and nodedij[i][ok]>envy_service_distance:
						obj-=nodes[i][3]*envy_objective_weight*(nodedij[i][ok]-envy_service_distance)*(nodedij[i][ok]-envy_service_distance)
					if envy_service_objective==1 and nodedij[i][nk]>envy_service_distance:
						obj+=nodes[i][3]*envy_objective_weight*(nodedij[i][nk]-envy_service_distance)*(nodedij[i][nk]-envy_service_distance)
					if envy_service_objective==4 and nodedij[i][ok]>envy_service_distance:
						obj-=nodes[i][3]*envy_objective_weight*(nodedij[i][ok]-envy_service_distance)
					if envy_service_objective==4 and nodedij[i][nk]>envy_service_distance:
						obj+=nodes[i][3]*envy_objective_weight*(nodedij[i][nk]-envy_service_distance)
					if envy_service_objective==2 and nodedij[i][ok]>envy_service_distance:
						envy-=nodes[i][3]*(nodedij[i][ok]-envy_service_distance)*(nodedij[i][ok]-envy_service_distance)
					if envy_service_objective==2 and nodedij[i][nk]>envy_service_distance:
						envy+=nodes[i][3]*(nodedij[i][nk]-envy_service_distance)*(nodedij[i][nk]-envy_service_distance)
				else:
					obj-=nodedik[i][ok]*travel_distance_weight
					if nodedij[i][ok]<=cflp_service_radius_preference:
						covered-=nodes[i][3]
					if nodedij[i][ok]>cflp_max_service_radius:
						not_covered-=nodes[i][3]
					if envy_service_objective==1 and nodedij[i][ok]>envy_service_distance:
						obj-=nodes[i][3]*envy_objective_weight*(nodedij[i][ok]-envy_service_distance)*(nodedij[i][ok]-envy_service_distance)
					if envy_service_objective==4 and nodedij[i][ok]>envy_service_distance:
						obj-=nodes[i][3]*envy_objective_weight*(nodedij[i][ok]-envy_service_distance)
					if envy_service_objective==2 and nodedij[i][ok]>envy_service_distance:
						envy-=nodes[i][3]*(nodedij[i][ok]-envy_service_distance)*(nodedij[i][ok]-envy_service_distance)
					for j in NearFacilityList[i]:
						if new_centersID[j]>=0:
							obj+=nodedik[i][j]*travel_distance_weight
							if nodedij[i][j]<=cflp_service_radius_preference:
								covered+=nodes[i][3]
							if nodedij[i][j]>cflp_max_service_radius:
								not_covered+=nodes[i][3]
							if envy_service_objective==1 and nodedij[i][j]>envy_service_distance:
								obj+=nodes[i][3]*envy_objective_weight*(nodedij[i][j]-envy_service_distance)*(nodedij[i][j]-envy_service_distance)
							if envy_service_objective==4 and nodedij[i][j]>envy_service_distance:
								obj+=nodes[i][3]*envy_objective_weight*(nodedij[i][j]-envy_service_distance)
							if envy_service_objective==2 and nodedij[i][j]>envy_service_distance:
								envy+=nodes[i][3]*(nodedij[i][j]-envy_service_distance)*(nodedij[i][j]-envy_service_distance)
							break
			obj-= penalty_on_demand * max(0,total_pop*cflp_min_service_coverage_percentage/100-objective_covered)
			obj+= penalty_on_demand * max(0,total_pop*cflp_min_service_coverage_percentage/100-covered)
			obj-= penalty_on_demand * objective_rmax_not_covered
			obj+= penalty_on_demand * not_covered
			if obj<old_obj: 
				best_exch.append([k,nk,obj])
	if best_exch==[]: 
		return 0
	best_exch.sort(key=lambda x:x[2])
	for x in best_exch[:1]:
		sol=node_groups[:]
		cid=centersID[:]
		obj=biobjective
		k=x[0]
		centersID[k]=-1
		nk=x[1]
		print [k,nk],
		centersID[nk]=facilityCandidate[nk]
		for i in range(num_units):
			for j in NearFacilityList[i]:
				if centersID[j]>=0:
					node_groups[i]=j
					break
		update_cflpr_district_info()
		print [k,nk],biobjective

		'''if adaptive_number_of_facilities==1 and biobjective>obj:
			node_groups=sol[:]
			centersID=cid[:]
			update_cflpr_district_info()
		if adaptive_number_of_facilities==0:
			nf=sum(1 for x in centersID if x>=0)
			if nf!=max_num_facility or biobjective>obj:
				node_groups=sol[:]
				centersID=cid[:]
				update_cflpr_district_info()'''
	if spatial_contiguity==1:
		repair_fragmented_solution()
	return 1

def pmp_envy_find(fi,facility2): #find fr for fi
	savings=0.0
	loss=[[x,0.0] for x in range(num_districts)]
	if fixed_cost_obj==1: 
		savings-=facilityCost[fi]
		loss=[[x,-facilityCost[x]] for x in range(num_districts)]
	if max_facility_cost>0 and adaptive_number_of_facilities==1:
		fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for k in range(num_districts):       
			fcost_new = fcost-facilityCost[k]+facilityCost[fi]
			loss[k][1]-= max(0,fcost-max_facility_cost)*penalty_on_demand
			loss[k][1]+= max(0,fcost_new-max_facility_cost)*penalty_on_demand
	w=travel_distance_weight
	for i in range(num_units):
		k=node_groups[i]
		if nodedik[i][fi]<nodedik[i][k]: 
			savings+=nodedik[i][k]*w-nodedik[i][fi]*w
		else:
			loss[k][1]+=min(nodedik[i][fi],nodedik[i][facility2[i]])*w-nodedik[i][k]*w
		if envy_service_objective==1:
			envy1=0.0
			envy2=0.0
			envy3=0.0
			d=nodedij[i][k]
			if d>envy_service_distance:
				envy1=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			d=nodedij[i][fi]
			if d>envy_service_distance:
				envy2=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			d=nodedij[i][facility2[i]]
			if d>envy_service_distance:
				envy3=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if nodedij[i][fi]<nodedij[i][k]:
				savings+=envy1-envy2
			else:
				loss[k][1]+=min(envy2,envy3)-envy1
		if envy_service_objective==4:
			envy1=0.0
			envy2=0.0
			envy3=0.0
			d=nodedij[i][k]
			if d>envy_service_distance:
				envy1=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			d=nodedij[i][fi]
			if d>envy_service_distance:
				envy2=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			d=nodedij[i][facility2[i]]
			if d>envy_service_distance:
				envy3=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			if nodedij[i][fi]<nodedij[i][k]:
				savings+=envy1-envy2
			else:
				loss[k][1]+=min(envy2,envy3)-envy1
	loss=[x for x in loss if centersID[x[0]]>=0]
	if len(loss)<1: return -1,-1.0
	loss.sort(key=lambda x:x[1])
	if facilityMinimumCapacity<0: #debuging
		shortage=0
		for k in range(num_districts):
			if centersID[k]>=0:
				shortage += max(0, facilityMinimumCapacity -district_info[k][1])
		for idx in range(len(loss)):
			caplist=[district_info[x][1] for x in range(num_districts)]
			fr=loss[idx][0]
			caplist[fr]=0
			for i in range(num_units):
				k=node_groups[i]
				if k!=fr: 
					if nodedij[i][fi]<nodedij[i][k]: 
						caplist[fi]+=nodes[i][3]
						caplist[k]-=nodes[i][3]
					continue              
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					if k==fr: continue
					if k==fi:
						caplist[fi]+=nodes[i][3]
						break
					caplist[k]+=nodes[i][3]
					break
			shortage2=0
			for k in range(num_districts):
				if caplist[k]>0:
					shortage2 += max(0, facilityMinimumCapacity -caplist[k])
			#print [sum(caplist),shortage,shortage2],[x for x in caplist if x>0]
			if shortage2<=shortage:
				#print [sum(caplist),shortage,shortage2],
				break             
			loss[idx][1]+= (shortage2-shortage) * penalty_on_demand
		loss.sort(key=lambda x:x[1])
	fr=loss[0][0]
	profit=savings-loss[0][1]
	return fr,profit
	


def pmp_find(fi,facility2): #find fr for fi
	if envy_service_objective==1:
		return pmp_envy_find(fi,facility2)
	if envy_service_objective==4:
		return pmp_envy_find(fi,facility2)
	savings=0.0
	loss=[[x,0.0] for x in range(num_districts)]
	if fixed_cost_obj==1: 
		savings=-facilityCost[fi]
		loss=[[x,-facilityCost[x]] for x in range(num_districts)]
	if max_facility_cost>0:
		fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for k in range(num_districts):       
			fcost_new = fcost-facilityCost[k]+facilityCost[fi]
			loss[k][1]-= max(0,fcost-max_facility_cost)*penalty_on_demand
			loss[k][1]+= max(0,fcost_new-max_facility_cost)*penalty_on_demand
	for i in range(num_units):
		k=node_groups[i]
		if nodedik[i][fi]<nodedik[i][k]: 
			savings+=nodedik[i][k]-nodedik[i][fi]
		else:
			loss[k][1]+=min(nodedik[i][fi],nodedik[i][facility2[i]])-nodedik[i][k]
	loss=[x for x in loss if centersID[x[0]]>=0]
	loss.sort(key=lambda x:x[1])
	if facilityMinimumCapacity<0: #debuging
		shortage=0
		for k in range(num_districts):
			if centersID[k]>=0:
				shortage += max(0, facilityMinimumCapacity -district_info[k][1])
		for idx in range(len(loss)):
			caplist=[district_info[x][1] for x in range(num_districts)]
			fr=loss[idx][0]
			caplist[fr]=0
			for i in range(num_units):
				k=node_groups[i]
				if k!=fr: 
					if nodedij[i][fi]<nodedij[i][k]: 
						caplist[fi]+=nodes[i][3]
						caplist[k]-=nodes[i][3]
					continue              
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					if k==fr: continue
					if k==fi:
						caplist[fi]+=nodes[i][3]
						break
					caplist[k]+=nodes[i][3]
					break
			shortage2=0
			for k in range(num_districts):
				if caplist[k]>0:
					shortage2 += max(0, facilityMinimumCapacity -caplist[k])
			#print [sum(caplist),shortage,shortage2],[x for x in caplist if x>0]
			if shortage2<=shortage:
				#print [sum(caplist),shortage,shortage2],
				break             
			loss[idx][1]+= (shortage2-shortage) * penalty_on_demand
	loss.sort(key=lambda x:x[1])
	fr=loss[0][0]
	profit=savings-loss[0][1]
	return fr,profit

def Renato_update(Facility2List,gainList,lossList,extraList): #bug
		for i in range(num_units):
			k1=node_groups[i]
			for k2 in NearFacilityList[i]:
				if centersID[k2]<0: continue
				if k2==k1: continue
				Facility2List[i]=k2
				break
		for k in range(num_districts):
			gainList[k]=0.0
			if centersID[k]>=0:continue
			for i in range(num_units):
				k1=node_groups[i]
				gainList[k] += max(0, nodedik[i][k1]-nodedik[i][k])
		for k in range(num_districts):
			lossList[k]=0.0
			if centersID[k]<0:continue
			ulist=[x for x in range(num_units) if node_groups[x]==k]
			for i in ulist:
				k2=Facility2List[i]
				lossList[k]+=nodedik[i][k2]-nodedik[i][k]
		for ki in range(num_districts):
			for kr in range(num_districts):
				extraList[ki][kr]=0.0
				if centersID[ki]>=0:continue
				if centersID[kr]<0:continue
				ulist=[x for x in range(num_units) if node_groups[x]==kr]
				for i in ulist:
					k2=Facility2List[i]
					if nodedij[i][ki]<nodedij[i][k2]:
						extraList[ki][kr]+=nodedik[i][k2]-max(nodedik[i][ki],nodedik[i][kr])

def robust_Renato_update(Facility2List,gainList,lossList,extraList,Kset):
	klist=range(len(Kset))
	for i in range(num_units):
		k1=node_groups[i]
		for k2 in NearFacilityList[i]:
			if centersID[k2]<0: continue
			if k2==k1: continue
			Facility2List[i]=k2
			break
	for s in klist:
		for k in range(num_districts):
			gainList[s][k]=0.0
			if centersID[k]>=0:continue
			for i in range(num_units):
				k1=node_groups[i]
				gainList[s][k] += max(0, (nodedij[i][k1]-nodedij[i][k])*Kset[s][i])
	for s in klist:
		for k in range(num_districts):
			lossList[s][k]=0.0
			if centersID[k]<0:continue
			ulist=[x for x in range(num_units) if node_groups[x]==k]
			for i in ulist:
				k2=Facility2List[i]
				lossList[s][k]+=(nodedij[i][k2]-nodedij[i][k])*Kset[s][i]
	for s in klist:
		for ki in range(num_districts):
			for kr in range(num_districts):
				extraList[s][ki][kr]=0.0
				if centersID[ki]>=0:continue
				if centersID[kr]<0:continue
				ulist=[x for x in range(num_units) if node_groups[x]==kr]
				for i in ulist:
					k2=Facility2List[i]
					if nodedij[i][ki]<nodedij[i][k2]:
						extra=nodedij[i][k2]-max(nodedij[i][ki],nodedij[i][kr])
						extraList[s][ki][kr]+=extra*Kset[s][i]

#On the implementation of a swap-based local search procedure for the p-median problem
#Renato&Werneck,2007
def pmp_Renato(Facility2List,gainList,lossList,extraList):
	#return pmp_TB()
	global node_groups
	global centersID
	global time_Whitaker
	obj0=biobjective    
	t=time.time()
	kiList=[x for x in range(num_districts) if centersID[x]<0]
	krList=[x for x in range(num_districts) if centersID[x]>=0]
	random.shuffle(kiList)
	random.shuffle(krList)
	improved=0
	bestSwap=[]
	bestprofit=0.0
	bestki=-1
	bestkr=-1
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	for kr in krList:
		for ki in kiList:
			profit=gainList[ki]-lossList[kr]+extraList[ki][kr]
			if max_facility_cost>0:
				extraCost1 = max(0,fcost-max_facility_cost)
				extraCost2 = max(0,fcost+facilityCost[ki]-facilityCost[kr]-max_facility_cost)
				if extraCost2>extraCost1+0.000001: continue
				profit+=(extraCost1-extraCost2)*penalty_on_demand
			if fixed_cost_obj==1:
				profit+=facilityCost[kr]-facilityCost[ki]
			if profit>0.000001: bestSwap.append([ki,kr,profit])
	if bestSwap==[]:return improved
	bestSwap.sort(key=lambda x:-x[2])
	idx=0
	#if len(bestSwap)>3:
	#   idx=random.randint(0,2) #elite improvement, select on from top three best swaps
	bestki=bestSwap[idx][0]
	bestkr=bestSwap[idx][1]
	bestprofit=bestSwap[idx][2]
   
	#print "solution update",bestki,bestkr,bestprofit,gainList[bestki],lossList[bestkr],extraList[bestki][bestkr],facilityCost[bestkr]-facilityCost[bestki],        
	# undo  gainList,lossList,extraList
	alist=[i for i in range(num_units) if node_groups[i]==bestkr or Facility2List[i]==bestkr or nodedij[i][bestki]<nodedij[i][Facility2List[i]] ]
	for i in alist:
		k1=node_groups[i]
		k2=Facility2List[i]
		d1=nodedik[i][k1]
		d2=nodedik[i][k2]
		lossList[k1]-=d2-d1
		for k in range(num_districts):
			if centersID[k]>=0: continue
			d=nodedik[i][k]
			if d<d2:
				gainList[k]-=max(0,d1-d)
				extraList[k][k1]-=d2-max(d,d1)
	#update solution
	centersID[bestkr]=-1
	centersID[bestki]=facilityCandidate[bestki]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
		k=node_groups[i]
		if k!=bestkr:
			if nodedij[i][k]>nodedij[i][bestki]: 
				node_groups[i]=bestki
		else:
			k=Facility2List[i]
			if nodedij[i][bestki]<nodedij[i][k]:
				k=bestki
			node_groups[i]=k
	#obj1=biobjective
	update_district_info()
	'''obj2=biobjective
	print "swap improve and ptofit:",obj1-obj2,bestprofit'''
	#update  Facility2List,gainList,lossList,extraList
	for i in range(num_units):
		k1=node_groups[i]
		for k2 in NearFacilityList[i]:
			if centersID[k2]<0: continue
			if k2==k1: continue
			Facility2List[i]=k2
			break
	for i in alist:
		k1=node_groups[i]
		k2=Facility2List[i]
		d1=nodedik[i][k1]
		d2=nodedik[i][k2]
		lossList[k1]+=d2-d1
		for k in range(num_districts):
			if centersID[k]>=0: continue
			d=nodedik[i][k]
			if d<d2:
				gainList[k]+=max(0,d1-d)
				extraList[k][k1]+=d2-max(d,d1)
	#Renato_update(Facility2List,gainList,lossList,extraList)
	update_district_info()
	improved=1
	time_Whitaker+=time.time()-t
	#if spatial_contiguity==1:
	#   repair_fragmented_solution()
	return improved


def robust_pmp_Renato(Facility2List,gainList,lossList,extraList,Kset,optK,objK):
	global node_groups
	global centersID
	global time_Whitaker
	obj0=biobjective    
	t=time.time()
	kiList=[x for x in range(num_districts) if centersID[x]<0]
	krList=[x for x in range(num_districts) if centersID[x]>=0]
	#random.shuffle(kiList)
	#random.shuffle(krList)
	improved=0
	bestSwap=[]
	bestprofit=0.0
	bestki=-1
	bestkr=-1
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	for kr in krList:  #testing...................................
		for ki in kiList:
			fprofit=0.0
			maxobj=0.0 
			if fixed_cost_obj==1:
				fprofit=facilityCost[kr]-facilityCost[ki]
			for k in range(len(Kset)):
				tprofit=gainList[k][ki]-lossList[k][kr]+extraList[k][ki][kr]
				newobj=objK[k]-fprofit-tprofit-optK[k]
				if newobj>maxobj: maxobj=newobj
				#print k,objK[k],fprofit,tprofit,optK[k]
			if maxobj<biobjective: 
				bestSwap.append([k,ki,kr,newobj,fprofit+tprofit])
				#print newobj,biobjective                
	if bestSwap==[]:return improved
	bestSwap.sort(key=lambda x:x[3])
	idx=0
	bestki=bestSwap[idx][1]
	bestkr=bestSwap[idx][2]
	bestprofit=bestSwap[idx][3]
	#print bestSwap[0],   
	#print "solution update",bestki,bestkr,bestprofit,gainList[bestki],lossList[bestkr],extraList[bestki][bestkr],facilityCost[bestkr]-facilityCost[bestki],        
	# undo  gainList,lossList,extraList
	alist=[i for i in range(num_units) if node_groups[i]==bestkr or Facility2List[i]==bestkr or nodedij[i][bestki]<nodedij[i][Facility2List[i]] ]
	for k in range(len(Kset)):
		for i in alist:
			k1=node_groups[i]
			k2=Facility2List[i]
			d1=Kset[k][i]*nodedij[i][k1]
			d2=Kset[k][i]*nodedij[i][k2]
			lossList[k][k1]-=d2-d1
			for j in range(num_districts):
				if centersID[j]>=0: continue
				d=Kset[k][i]*nodedij[i][j]
				if d<d2:
					gainList[k][j]-=max(0,d1-d)
					extraList[k][j][k1]-=d2-max(d,d1)
	#update solution
	centersID[bestkr]=-1
	centersID[bestki]=facilityCandidate[bestki]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
		k=node_groups[i]
		if k!=bestkr:
			if nodedij[i][k]>nodedij[i][bestki]: 
				node_groups[i]=bestki
		else:
			k=Facility2List[i]
			if nodedij[i][bestki]<nodedij[i][k]:
				k=bestki
			node_groups[i]=k
	for i in range(num_units):
		k1=node_groups[i]
		for k2 in NearFacilityList[i]:
			if centersID[k2]<0: continue
			if k2==k1: continue
			Facility2List[i]=k2
			break
	for i in alist:
		k1=node_groups[i]
		k2=Facility2List[i]
		for k in range(len(Kset)):
			d1=nodedij[i][k1]*Kset[k][i]
			d2=nodedij[i][k2]*Kset[k][i]
			lossList[k][k1]+=d2-d1
			for j in range(num_districts):
				if centersID[j]>=0: continue
				d=nodedij[i][j]*Kset[k][i]
				if d<d2:
					gainList[k][j]+=max(0,d1-d)
					extraList[k][j][k1]+=d2-max(d,d1)
	#Renato_update(Facility2List,gainList,lossList,extraList)
	#print "biobjective",biobjective,
	update_robust_obj(Kset,optK,objK)
	#print biobjective,len(bestSwap),bestSwap[:5]
	#print [bestSwap[0][0],int(bestSwap[0][3]),int(bestSwap[0][4])],
	improved=1
	time_Whitaker+=time.time()-t
	#if spatial_contiguity==1:
	#   repair_fragmented_solution()
	return improved

#Whitaker,1983
def pmp_Whitaker():
	#return pmp_TB()
	global node_groups
	global centersID
	global time_Whitaker
	#global TB_tabu_list
	#if centersID in TB_tabu_list: return -1
	t=time.time()
	facility2=[0 for x in range(num_units)] #num_districts
	for i in range(num_units):
		k1=node_groups[i]
		for k2 in NearFacilityList[i]:
			if centersID[k2]>=0 and k2!=k1: 
				facility2[i]=k2
				break
	klist=[x for x in range(num_districts) if centersID[x]<0]
	random.shuffle(klist)
	improved=0
	best_swap=[-1,-1,0.00001]
	swap=[]
	for nk in klist:
		k,profit=pmp_find(nk,facility2)
		if profit<=0.00001: continue
		swap.append([k,nk,profit])
		if profit>best_swap[2]:
			best_swap[0]=k
			best_swap[1]=nk
			best_swap[2]=profit
		#if len(swap)>=1:
		#   break
	swap.sort(key=lambda x:-x[2])
	if best_swap[0]>=0:
		#k=best_swap[0]
		#nk=best_swap[1]
		idx=0
		if len(swap)>2:
			idx=random.randint(0,1)
		idx=0 #best acceptance
		k=swap[idx][0]
		nk=swap[idx][1]
		centersID[k]=-1
		centersID[nk]=facilityCandidate[nk]
		for i in range(num_units):
			j=node_groups[i]
			if j!=k:
				if nodedik[i][j]>nodedik[i][nk]: node_groups[i]=nk
			else:
				for j in NearFacilityList[i]:
					if centersID[j]>=0:
						node_groups[i]=j
						break
		update_district_info()
		#print [x for x in centersID if x>=0]
		improved=1
	time_Whitaker+=time.time()-t
	#if spatial_contiguity==1:
	#   repair_fragmented_solution()
	#if improved==-1: 
	#    if centersID not in TB_tabu_list: TB_tabu_list.append(centersID[:])
	#print best_swap[2],
	return improved


def pmp_TB2():
	global node_groups
	global centersID
	global TB_tabu_list
	best_exch=[] #klist,save
	best_obj=biobjective-0.00001
	counts=[[x,0] for x in range(num_districts)]  
	for x in all_solutions:
		for i in range(num_districts):
			if x[1][i]>=0: counts[i][1]+=1
	counts.sort(key=lambda x:-x[1])
	while counts[-1][1]==0: counts.pop()
	list_h=[x[0] for x in counts[:max_num_facility*2/3] ]
	clist=[x for x in range(num_districts) if centersID[x]>=0 and x not in list_h]
	klist=[x[0] for x in counts]
	random.shuffle(clist)
	random.shuffle(klist)
	#print klist
	for k in clist:
		for nk in klist:
			if nk in clist: continue
			obj=0.0
			nklist=clist[:]
			nklist.remove(k)
			nklist.append(nk)
			#for i in range(num_units):
			#    obj+=min(nodedik[i][x] for x in nklist)
			ulist=[x for x in range(num_units) if node_groups[x]==k]
			for i in ulist:
				obj+=min(nodedik[i][x] for x in nklist)
			ulist=[x for x in range(num_units) if node_groups[x]!=k]
			for i in ulist:
				c=node_groups[i]
				obj+=min(nodedik[i][c], nodedik[i][nk])
			if obj<best_obj: 
				best_obj=obj
				best_exch=[k,nk]
		#if best_exch!=[]: break
		#if best_obj-biobjective<-biobjective*0.001: break
	if best_exch==[]: 
		#TB_tabu_list.append(centersID[:])
		#print "tabu len=",len(TB_tabu_list)
		return -1
	#print best_exch,best_obj,biobjective
	k=best_exch[0]
	centersID[k]=-1
	k=best_exch[1]
	centersID[k]=facilityCandidate[k]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	if spatial_contiguity>=1: repair_fragmented_solution()
	k1=best_exch[0]
	k2=best_exch[1]
	return 1


def assign_sub_mst(dlist,ulist):
	vars=[]
	for i in ulist:
		k=node_groups[i]
		if k<0: continue
		v='x_'+str(i)+ '_'+ str(k)
		vars.append([v,1])
	return vars


# search upper bound with LR results
def upper_bound_CFLP(yobj,ylist,xijlist,gi):
	global node_groups
	global centersID
	global district_info
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	supply=0
	total_fcost=[facilityCapacity[x] for x in range(num_districts) if yobj[x]<0]
	total_tcost=0.0
	for k in range(num_districts):
		if yobj[x]>=0: continue
		total_tcost += sum(xijlist[k][x]* nodedik[x][k] for x in range(num_units))

	for k in range(num_districts):
		district_info[k][1]=0
		district_info[k][3]=0
		if yobj[k]<0:
			centersID[k]=facilityCandidate[k]
			district_info[k][3]=facilityCapacity[k]
			supply+=facilityCapacity[k]
			#if supply>=total_pop and total_fcost>total_tcost: break
	if supply<total_pop:
		faclist=[[k,yobj[k]] for k in range(num_districts) if yobj[k]>=0]
		faclist.sort(key=lambda x: x[1])
		while 1:
			r=random.random()
			idx=int((r*r*0.9999*len(faclist)))
			k=faclist[idx][0]
			if centersID[k]>=0: continue
			centersID[k]=facilityCandidate[k]
			district_info[k][3]=facilityCapacity[k]
			supply+=facilityCapacity[k]
			if supply>=total_pop: break
	#delete overlap location
	supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)
	if adaptive_number_of_facilities==1:
		for i in range(num_districts):
			if centersID[i]<0: continue
			ilist=[ x for x in range(num_units) if xij[i][x]==1]
			for j in range(num_districts):
				if centersID[j]<0: continue
				if i==j: continue
				jlist=[ x for x in range(num_units) if xij[j][x]>=0.0001]
				cover=1
				for u in jlist:
					if u not in ilist:
						cover=0
						break
				if cover==1: 
					#print "overlayed",i,j
					centersID[j]=-1
					district_info[j][3]=0
					supply-=facilityCapacity[j]
					break
	if spatial_contiguity>=1:
		for k in range(num_districts):
			if centersID[k]>=0:
				i=nearCustomer[k]
				node_groups[i]=k
				district_info[k][1]+=nodes[i][3]
	for i in range(num_units):
		if node_groups[i]>=0: continue
		#klist=[[x,nodedik[i][x]/xijlist[x][i]] for x in range(num_districts) if xijlist[x][i] > 0.99 and centersID[x]>=0 and yobj[x]<0] #0.66
		klist=[[x,nodedik[i][x]] for x in range(num_districts) if xijlist[x][i] > 0.999 and centersID[x]>=0 and yobj[x]<0] #0.66
		if len(klist)==0: continue
		klist.sort(key=lambda x:x[1])
		k=klist[0][0]
		node_groups[i]=k
		district_info[k][1]+=nodes[i][3]

	#assign large unit at first, this tends to a feasible solution
	ulist=[ [x,nodes[x][3]] for x in range(num_units) if node_groups[x]==-1]
	ulist.sort(key=lambda x: -x[1])
	ulist=[x[0] for x in ulist]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if district_info[k][1] + nodes[i][3] <= district_info[k][3]:
				district_info[k][1]+=nodes[i][3]
				node_groups[i]=k
				break
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	pop=sum(nodes[x][3] for x in ulist)
	if adaptive_number_of_facilities==1 and supply<total_pop:
		best_new_facility=-1
		best_new_cost=MAXNUMBER
		for k in range(num_districts):
			if centersID[k]>=0:continue
			if facilityCapacity[k]<pop: continue
			if supply+facilityCapacity[k]<total_pop: continue
			new_cost=facilityCost[k]
			new_cost+=sum(nodedik[x][k] for x in ulist)
			if new_cost<best_new_cost:
				best_new_cost=new_cost
				best_new_facility=k
		if best_new_facility!=-1:
			centersID[best_new_facility]=facilityCandidate[best_new_facility]
			district_info[best_new_facility][3]=facilityCapacity[best_new_facility]
			for x in ulist: node_groups[x]=best_new_facility
	#assign the remaining units
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			district_info[k][1]+=nodes[i][3]
			break
	#print len(ulist), sum(nodes[x][3] for x in ulist)
	delete_empty_facility()
	update_district_info()
	update_best_solution()
	#repair_fragmented_solution()
	VND_local_search()
	delete_empty_facility()
	update_district_info()
	update_district_info()
	update_best_solution()
	#print biobjective,
	if is_spp_modeling==1: update_region_pool_all() 
	#print "biobjective",biobjective    
	return biobjective

def LR_main(loops):
	if location_problem==0: return AP_LR_main(loops,0.0001,0.0001)
	if location_problem==1: 
		if adaptive_number_of_facilities==1: 
			#location_construction_random()
			return CFLP_LR_main(loops)
		if adaptive_number_of_facilities==0: return CKFLP_LR_main(loops)
	if location_problem==2: return CKFLP_LR_main(loops)
	#if location_problem==3: return CKFLP_LR_main(loops)
multiplier=[]
yj=[]
xij=[]
subobj=[]
max_exclusion_list=[]
max_inclusion_list=[]
exclusion=[]
inclusion=[]

#LR for classical CFLP
def CFLP_LR_main(loops):
	global node_groups
	global centersID
	global multiplier
	global exclusion
	global inclusion
	global max_exclusion_list
	global max_inclusion_list
	global yj
	global xij
	global subobj
	global all_solutions
	global spatial_contiguity
	global potential_facilities
	max_exclusion_list=[0.0 for k in range(num_districts)]
	max_inclusion_list=[0.0 for k in range(num_districts)]
	flist=[]
	xijlist=[]
	nf=num_districts/2-int(num_districts*total_pop/sum(facilityCapacity))/2
	#maxr=sum(sum(x) for x in nodedij)/num_districts/num_units
	#r=maxr/math.sqrt(nf*1.0)
	#multiplier=[r*nodes[x][3]*(49.5+random.random())/50 for x in range(num_units)]
	multiplier=[0.0 for x in range(num_units)]
	unitcost=sum(facilityCost)*1.0/sum(facilityCapacity)
	for i in range(num_units):
		k=NearFacilityList[i][1]
		ui=nodedik[i][k]+nodes[i][3]*unitcost
		multiplier[i]=ui*(49.5+random.random())/50
	#print "multiplier",multiplier
	subobj=[0.0 for x in range(num_districts)]
	xij=[[] for x in range(num_districts)]
	yj=[0 for x in range(num_districts)]
	gi=[1.0 for  x in range(num_units)]
	gi_possibility=gi[:]
	ub=sum(facilityCost)*total_pop/sum(facilityCapacity)+sum(multiplier)
	ub=sum(facilityCost)+sum(nodedik[x][NearFacilityList[x][-1]] for x in range(num_units))+sum(multiplier)
	unf=num_districts
	fub=ub
	unf=sum(1 for x in centersID if x>=0)
	lb=-MAXNUMBER
	delta1=0.001
	delta2=0.01
	alpha=1.0
	old_multiplier=multiplier[:]
	best_yj=yj[:]
	best_xij=copy.deepcopy(xij)
	best_multiplier=multiplier[:]
	improved_lb=1
	improved_ub=1
	best_lb_list=[]
	exclusion=[x for x in range(num_districts) if x not in potential_facilities]
	inclusion=[]
	not_improve=0
	loop=0
	while(1):
		loop+=1
		old_multiplier=multiplier[:]
		old_gi=gi[:]
		rlist=[]
		for k in range(num_districts):
			if k in exclusion:
				subobj[k]=MAXNUMBER
				xij[k]=[0.0 for x in range(num_units)]
				yj[k]=0
				continue
			obj,y,xi=sub_CFLP_LR(k)
			#print "lr",k, obj,y,xi           
			subobj[k]=obj
			xij[k]=xi[:]
			yj[k]=y

		flb=sum(x for x in subobj if x<0)+sum(multiplier)#[x] for x in range(num_units) if gi[x]<=0)
		#Facility exclusion, Holmberg,1999
		for k in range(num_districts):
			if subobj[k]<MAXNUMBER and flb+subobj[k]>max_exclusion_list[k]: 
				max_exclusion_list[k]=flb+subobj[k] #??? instance p43
			if subobj[k]<MAXNUMBER and flb+subobj[k]>ub:
				if k not in exclusion: exclusion.append(k)
			if subobj[k]<0 and flb-subobj[k]>ub:
				if k not in inclusion: inclusion.append(k)
			if subobj[k]<0 and flb-subobj[k]>max_inclusion_list[k]: 
				max_inclusion_list[k]=flb - subobj[k] #???
		#supply > demand
		num=sum(1 for x in subobj if x<0)
		total_supply=sum(facilityCapacity[x] for x in range(num_districts) if subobj[x]<0)
		for i in range(num_units):
			g=1.0
			for k in range(num_districts):
				if subobj[k]>0: continue
				g-=xij[k][i]
			gi[i]=g
		norm=sum(gi[x]*gi[x] for x in range(num_units))/num_units
		#flb-=sum(gi[x]*avg_dis_min*nodes[x][3] for x in range(num_units) if gi[x]>0)
		#print norm, total_supply, total_pop,
		total_supply=sum(facilityCapacity[x] for x in range(num_districts) if subobj[x]<=0)
		if total_supply>=total_pop:
			best_lb_list.append([subobj[:],yj[:],copy.deepcopy(xij)])
			best_lb_list.sort(key=lambda x: x[0])
			if len(best_lb_list)>10: del best_lb_list[-1]
		not_improve+=1
		improved_lb+=1
		#print lb,flb,
		if flb>lb:# and total_supply>=total_pop:
			improved_lb=0
			not_improve -= int((flb-lb)*10000.0/abs(lb))
			if not_improve<0: not_improve=0
			lb=flb
			d=sum(old_gi[x]*gi[x] for x in range(num_units))
			if d>=0.0:
				alpha*=1.1
				if alpha>2: alpha=2.0
		if improved_lb%10==9:
			alpha*=0.66
		cap=sum(facilityCapacity[x] for x in range(num_districts) if subobj[x]<=0)

		if (loop==20 or improved_lb==0) and loop>=20:
			#if cap>-1000000:#cap>=total_pop:
				obj=upper_bound_CFLP(subobj,yj,xij,gi)
				if obj>0.000001:
					all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
					#update_region_pool_all()
		
		fub=biobjective
		nf=sum(1 for x in range(num_districts) if subobj[x]<=0)
		if fub>0 and fub<ub:
			not_improve -=int((ub-fub)*10000.0/ub )
			if not_improve<0: not_improve=0
			ub=fub
			unf=sum(1 for x in range(num_districts) if centersID[x]>=0)
		#update multiplier  
		sq=sum(x*x for x in gi)
		if abs(sq)<0.001:
			#for k in range(num_districts):
			#    if flb+subobj[k]>max_exclusion_list[k]: max_exclusion_list[k]=flb+subobj[k] #??? instance p43
			if len(all_solutions)<=0:
				obj=upper_bound_CFLP(subobj,yj,xij,gi)
				if obj>0.00001:
					all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
					#update_region_pool_all()
			break
		#print gi
		t=alpha*(ub-flb)/sq
		for i in range(num_units):
			multiplier[i]+=t*gi[i]
			#if cap<total_pop: multiplier[i]*=1.01
			if multiplier[i]<0.0:
				multiplier[i]=0.0
				if gi[0]>0.999: 
					n=nf/3
					if n==0: continue
					s=0.0
					klist=[x for x in NearFacilityList[i] if subobj[x]<=0]
					r=sum(nodedik[i][x] for x in klist[:n])/n
					multiplier[i]=r
		cap=sum(facilityCapacity[x] for x in range(num_districts) if subobj[x]<=0)
		cost=sum(facilityCost[x] for x in range(num_districts) if yj[x]==1)

		viol=sum(1 for x in gi if abs(x)>0.5)
		viol1=sum(1 for x in gi if x>0.5)
		viol2=sum(1 for x in gi if x<-0.5)

		s=str(loop)+" bestub: "+str(unf)+" "+str(int(ub)) + " ub: "+str(int(fub))
		s+=" bestlb: " +str(int(lb)) + " lb: " +str(nf) +" " +str(int(flb)) 
		#s+=" bestlb: " +str(int(lb)) + " lb: " +str(nf)+" "+str(viol)+" "+str(viol1)+" "+str(viol2)+" " + str(int(norm*100))+" "
		#s+=str(int(flb)) +" "+ str(cap)+" " +str(int(alpha*100000)/100000.0) +" "+str(len(exclusion))
		s+=" "+str(not_improve)
		arcpy_print(s)
		if improved_lb>=100 or not_improve>loops or loop>800: 
			break
		if ub<lb:
			print "debug: LR, ub<lb!!",ub,lb
			print sum(x for x in subobj if x<=0)+sum(multiplier)
			print subobj
			print multiplier
		#if ub>0 and(ub-lb)/ub<0.0005:
		#    break
		if norm<0.01: break
		if stop_searching==1: break
	   
	#print all_solutions
	all_solutions.sort(key=lambda x:x[0])
	all_solutions=pop_selection(all_solutions)
	#while len(all_solutions)>max(multi_start_count*2,5): all_solutions.pop()
	while len(all_solutions)>multi_start_count*2: all_solutions.pop()
	#spatial_contiguity=spatial_contiguity_tmp
	#potential_facilities=[x for x in range(num_districts) if x not in exclusion]
	potential_facilities=[x for x in range(num_districts)]

def sub_CFLP_LR(idx):
	udlist=[[i,(nodedik[i][idx]-multiplier[i])/nodes[i][3]] for i in range(num_units) if nodedik[i][idx]<= multiplier[i]]
	#udlist=[[i,(nodedik[i][idx]-multiplier[i])] for i in range(num_units) if nodedik[i][idx]<= multiplier[i]]
	udlist.sort(key=lambda x: x[1])
	demand=0
	xlist=[0.0 for i in range(num_units)]
	f=facilityCost[idx]*fixed_cost_obj
	for i in range(len(udlist)):
		u=udlist[i][0]
		if demand+nodes[u][3]<=facilityCapacity[idx]:
			demand+=nodes[u][3]
			f+=nodedik[u][idx]-multiplier[u]
			xlist[u]=1.0
		else:
			r=(facilityCapacity[idx]-demand)*1.0/nodes[u][3]
			f+=r*(nodedik[u][idx]-multiplier[u])
			xlist[u]=r
			break
	#if f>=0.0:
	#    return 0.0,0,[0.0 for i in range(num_units)]
	#print "sub_lr",idx,f, xlist   
	return f,1,xlist

# search upper bound with best LR solutions 
def upper_bound_CKFLP(ylist,xijlist):
	global node_groups
	global centersID
	global all_solutions
	global district_info
	if sum(ylist)<1: return MAXNUMBER
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	for k in range(num_districts):
		district_info[k][1]=0
		district_info[k][3]=0
		if ylist[k]==1:
			centersID[k]=facilityCandidate[k]
			district_info[k][3]=facilityCapacity[k]
	#assign demand units with integer xij in LR solution
	#assign near unit to facility
	fulist=[]    
	if spatial_contiguity ==1:
		for k in range(num_districts):
			if ylist[k]==1:
				i=nearCustomer[k]
				node_groups[i]=k
				district_info[k][1]+=nodes[i][3]
				fulist.append(i)
	for i in range(num_units):
		if i in fulist: continue
		klist=[[x,nodedik[i][x] ] for x in range(num_districts) if xijlist[x][i] > 0.99] #0.66
		if len(klist)==0: continue
		klist.sort(key=lambda x: x[1])
		for x in klist:
			k=x[0]
			if centersID[k]<0: continue
			if district_info[k][1] + nodes[i][3] <= district_info[k][3]:
				node_groups[i]=k
				district_info[k][1]+=nodes[i][3]
				break
	#assign large unit at first
	ulist=[ [x,nodes[x][3]] for x in range(num_units) if node_groups[x]==-1]
	ulist.sort(key=lambda x: -x[1])
	ulist=[x[0] for x in ulist]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if district_info[k][1] + nodes[i][3] <= district_info[k][3]:
				district_info[k][1]+=nodes[i][3]
				node_groups[i]=k
				break
	#assign demand units
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			district_info[k][1]+=nodes[i][3]
			break
	if adaptive_number_of_facilities==1: delete_empty_facility()
	update_district_info()
	VND_local_search()
	cost=objective
	cost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)
	if is_spp_modeling==1: update_region_pool_all()
	return biobjective
#LR for CKFLP
def CKFLP_LR_main(loops):
	global node_groups
	global centersID
	global multiplier
	global yj
	global xij
	global subobj
	global all_solutions
	global spatial_contiguity
	global max_exclusion_list
	global max_inclusion_list
	max_exclusion_list=[0.0 for k in range(num_districts)]
	max_inclusion_list=[0.0 for k in range(num_districts)]
	#spatial_contiguity_tmp=spatial_contiguity
	#spatial_contiguity=0
	flist=[]
	xijlist=[]
	nf=max_num_facility
	multiplier=[0.0 for x in range(num_units)]
	unitcost=sum(facilityCost)*1.0/sum(facilityCapacity)
	for i in range(num_units):
		k=NearFacilityList[i][1]
		ui=nodedik[i][k]+nodes[i][3]*unitcost
		multiplier[i]=ui*(49.5+random.random())/50
	subobj=[0.0 for x in range(num_districts)]
	xij=[[] for x in range(num_districts)]
	yj=[0 for x in range(num_districts)]
	gi=[1.0 for  x in range(num_units)]
	gi_possibility=gi[:]
	#ub=sum(facilityCost)+sum(multiplier)
	ub=sum(facilityCost)*total_pop/sum(facilityCapacity)+sum(multiplier)
	fub=ub
	unf=sum(1 for x in centersID if x>=0)
	#all_solutions.append([biobjective,centersID[:],node_groups[:],0,0,0,0,0])
	lb=-MAXNUMBER
	delta1=0.001
	delta2=0.01
	alpha=1.0
	old_multiplier=multiplier[:]
	best_yj=yj[:]
	best_xij=copy.deepcopy(xij)
	best_multiplier=multiplier[:]
	improved_lb=0
	improved_ub=0
	last_ji=[]
	best_lb_list=[]
	exclusion=[]
	for loop in range(loops*5):
		#search lower bound
		old_multiplier=multiplier[:]
		old_gi=gi[:]
		rlist=[]
		for k in range(num_districts):
			if k in exclusion:
				subobj[k]=0.0
				xij[k]=[0.0 for x in range(num_units)]
				yj[k]=0
			obj,y,xi=sub_CKFLP_LR(k)
			subobj[k]=obj
			xij[k]=xi[:]
			yj[k]=y

		flb=sum(x for x in subobj if x<0)+sum(multiplier)#[x] for x in range(num_units) if gi[x]<=0)
		for k in range(num_districts):
			if flb+subobj[k]>max_exclusion_list[k] and subobj[k]<0:max_exclusion_list[k]=flb+subobj[k] #???
			if flb+subobj[k]>ub:
				if k not in exclusion: exclusion.append(k)
			if flb-subobj[k]>ub:
				if k not in inclusion: inclusion.append(k)
			if flb-subobj[k]>max_inclusion_list[k] and subobj[k]<0: max_inclusion_list[k]=flb-subobj[k] #???

		num=sum(1 for x in subobj if x<0)
		total_supply=sum(facilityCapacity[x] for x in range(num_districts) if subobj[x]<0)
		if num!=max_num_facility:
			select_LR_facility()
		else:
			for k in range(num_districts):
				if subobj[k]>0:
					subobj[k]=0.0
					yj[k]=0
					xij[k]=[0.0 for x in range(num_units)]
		for i in range(num_units):
			g=1.0
			for k in range(num_districts):
				g-=xij[k][i]
			gi[i]=g
		#flb=sum(subobj)+sum(multiplier)
		norm=sum(gi[x]*gi[x] for x in range(num_units))
		total_supply=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
		if total_supply>=total_pop-0.00001:
			best_lb_list.append([norm,yj[:],copy.deepcopy(xij)])
			best_lb_list.sort(key=lambda x: x[0])
			if len(best_lb_list)>10: del best_lb_list[-1]
		#print total_supply
		improved_lb+=1
		if flb>lb+0.0000001:
			lb=flb
			improved_lb=0
			d=sum(old_gi[x]*gi[x] for x in range(num_units))
		if improved_lb%15==14:
			alpha*=0.66
		cap=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
		cost=sum(facilityCost[x] for x in range(num_districts) if yj[x]==1)
		if (improved_lb==0 or improved_lb%20==0) and loop>=20:
			if improved_lb==0 and cap>total_pop:
				upper_bound_CKFLP(yj,xij)
				#print "*",
			else:
				if len(best_lb_list)>0:
					r=random.random()
					idx=int(r*r*0.999*len(best_lb_list))
					idx=0
					upper_bound_CKFLP(best_lb_list[idx][1],best_lb_list[idx][2])
					del best_lb_list[idx]
					#print "#",
			all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
			fub=biobjective
			nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
			cap=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
			cost=sum(facilityCost[x] for x in range(num_districts) if yj[x]==1)
			improved_ub+=1
			if fub<ub:
				ub=fub
				unf=nf
				alpha*=1.1
				improved_ub=0
		#update multiplier  
		sq=sum(x*x for x in gi)
		if abs(sq)<0.001:
			break
		t=alpha*(ub-flb)/sq
		for i in range(num_units):
			multiplier[i]+=t*gi[i]
			if multiplier[i]<0.0:
				multiplier[i]=0.0
		viol=sum(1 for x in gi if abs(x)>0.5)
		s="CPMP_LR "+str(loop)+" bestub: "+str(unf)+" "+str(int(ub)) + " ub: "+str(int(fub))
		s+=" bestlb: " +str(int(lb)) + " lb: " +str(sum(yj))+" " +str(int(flb))
		#s+=" bestlb: " +str(int(lb)) + " lb: " +str(sum(yj))+" "+str(viol)+" " + str(int(norm))+" "
		#s+=str(int(flb)) +" "+ str(cap)+" " +str(int(alpha*100000)/100000.0) +" "+str(len(exclusion))
		arcpy_print(s)
		if abs(lb-ub)/ub<delta1:
			break
		if improved_lb>=loops: 
			break
	all_solutions.sort(key=lambda x:x[3]+x[4]+x[5]*2*avg_dis_min+x[6]*penalty_on_demand)
	#all_solutions.sort(key=lambda x:x[0])
	all_solutions=pop_selection(all_solutions)
	while len(all_solutions)>multi_start_count*2: all_solutions.pop()
	#while len(all_solutions)>5: all_solutions.pop()
	#spatial_contiguity=spatial_contiguity_tmp

def select_LR_facility():
	global subobj
	global yj
	global xij
	rlist=[[x,subobj[x],facilityCapacity[x],0.0 ] for x in range(num_districts) if yj[x]==1]
	rlist.sort(key=lambda x: x[1])
	if adaptive_number_of_facilities==1:
		klist=[x[0] for x in rlist if x[1]<0]
		random.shuffle(klist)
		clist=[x[0] for x in rlist if x[1]>=0]
		random.shuffle(clist)
		supply=sum(facilityCapacity[x] for x in klist)
		for x in klist:
			succ=0
			for y in clist:
				if supply-facilityCapacity[x]+facilityCapacity[y]>=total_pop:
					klist.remove(x)
					klist.append(y)
					succ=1
					break
			if succ==1: break
		for k in range(num_districts):
			if k in klist:
				yj[k]=1
			else:
				yj[k]=0
				subobj[k]=MAXNUMBER
		#print klist,sum(facilityCapacity[x] for x in klist),sum(facilityCost[x] for x in klist)
		return subobj,yj,xij
		
	klist1=[rlist[x][0] for x in range(max_num_facility)]
	supply=sum(facilityCapacity[x] for x in klist1)
	#print supply,
	if supply>=total_pop:
		for k in range(num_districts):
			subobj[k]=min(0.0,subobj[k])
			if yj[k]==0: continue
			if k not in klist1:
				yj[k]=0
				#subobj[k]=0.0
				for i in range(num_units):
					 xij[k][i]=0.0
		return subobj,yj,xij

	rlist.sort(key=lambda x: -x[2])
	flist=[x[0] for x in rlist]
	klist=[rlist[x][0] for x in range(max_num_facility)]
	#obj=sum(subobj[x] for x in klist)
	rlist.sort(key=lambda x: x[1])
	while 1:
		imp=0
		supply=sum(facilityCapacity[x] for x in klist)
		for k1 in flist:
			if k1 not in klist: continue
			for k2 in flist:
				if k2 in klist: continue
				if supply -facilityCapacity[k1]+facilityCapacity[k2]<min(total_pop,supply): continue
				if subobj[k2]<subobj[k1]:
					#print ".",
					klist.remove(k1)
					klist.append(k2)
					imp=1
					supply=sum(facilityCapacity[x] for x in klist)
					k1=k2
		if imp==0:
			break
		break
	#random.shuffle(rlist)
	supply=sum(facilityCapacity[x] for x in klist)
	#print supply

	for k in range(num_districts):
		subobj[k]=min(0.0,subobj[k])
		if yj[k]==0: continue
		if k not in klist:
			yj[k]=0
			xij[k]=[0.0 for i in range(num_units)]
	s=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
	c=sum(facilityCost[x] for x in range(num_districts) if yj[x]==1)
	#print s,c,
	return subobj,yj,xij

def sub_CKFLP_LR(idx):
	udlist=[[i,(nodedik[i][idx]-multiplier[i])/nodes[i][3]] for i in range(num_units) if nodedik[i][idx]<= multiplier[i]]
	udlist.sort(key=lambda x: x[1])
	demand=0
	xlist=[0.0 for i in range(num_units)]
	alpha=1.0
	if location_problem==2:
		alpha=1.0+pop_deviation
	f=facilityCost[idx]*fixed_cost_obj
	for x in udlist:
		u=x[0]
		if demand+nodes[u][3]<=facilityCapacity[idx]*alpha:
			demand+=nodes[u][3]
			xlist[u]=1.0
			f+=nodedik[u][idx]-multiplier[u]
		else:
			xlist[u]=(facilityCapacity[idx]*alpha-demand)*1.0/nodes[u][3]
			f+=(nodedik[u][idx]-multiplier[u])*xlist[u]
			break
	#demand=sum( nodes[x][3]*xlist[x] for x in range(num_units) )
	#if demand > facilityCapacity[idx]:
	#    print "debug", idx, facilityCapacity[idx], demand, xlist
	#if f>=0.0:
	#    return 0.0,0,[0 for i in range(num_units)]
	return f,1,xlist

#LR for CKFLP
def CPMP_LR_main(loops):
	global node_groups
	global centersID
	global multiplier
	global yj
	global xij
	global subobj
	global all_solutions
	global spatial_contiguity
	global max_exclusion_list
	global max_inclusion_list
	max_exclusion_list=[0.0 for k in range(num_districts)]
	max_inclusion_list=[0.0 for k in range(num_districts)]
	#spatial_contiguity_tmp=spatial_contiguity
	#spatial_contiguity=0
	flist=[]
	xijlist=[]
	nf=max_num_facility
	if adaptive_number_of_facilities==1:
		print "debug: using CFLP_LR_main!!!"
		return 0
	maxr=0.0
	for i in range(num_units):
		maxr=max(maxr, max(nodedij[i]) )
	r=maxr/math.sqrt(nf*1.0)
	multiplier=[r*nodes[x][3] for x in range(num_units)]
	subobj=[0.0 for x in range(num_districts)]
	xij=[[] for x in range(num_districts)]
	yj=[0 for x in range(num_districts)]
	gi=[1.0 for  x in range(num_units)]
	ub=sum(multiplier)
	fub=ub
	unf=sum(1 for x in centersID if x>=0)
	#all_solutions.append([biobjective,centersID[:],node_groups[:],0,0,0,0,0])
	lb=-MAXNUMBER
	delta1=0.001
	delta2=0.01
	alpha=1.0
	old_multiplier=multiplier[:]
	best_yj=yj[:]
	best_xij=copy.deepcopy(xij)
	best_multiplier=multiplier[:]
	improved_lb=0
	improved_ub=0
	last_ji=[]
	best_lb_list=[]
	exclusion=[]
	loop=0
	while 1:
		#search lower bound
		loop+=1
		old_multiplier=multiplier[:]
		old_gi=gi[:]
		rlist=[]
		cost=0
		#cost=ub/nf
		for k in range(num_districts):
			'''if k in exclusion:
				subobj[k]=0.0
				xij[k]=[0.0 for x in range(num_units)]
				yj[k]=0'''
			obj,y,xi=sub_CKFLP_LR(k)
			subobj[k]=obj+cost
			xij[k]=xi[:]
			yj[k]=y
		#print subobj
		objlist=[[k,subobj[k]] for  k in range(num_districts)]
		objlist.sort(key=lambda x:x[1])
		flb=sum(x[1] for x in objlist[:nf])+sum(multiplier) -cost*nf
		#[x] for x in range(num_units) if gi[x]<=0)
		for k in range(num_districts):
			if flb+subobj[k]>max_exclusion_list[k]: max_exclusion_list[k]=flb+subobj[k] #??? instance p43
			if flb+subobj[k]>ub:
				if k not in exclusion: exclusion.append(k)
			if flb-subobj[k]+cost>ub:
				if k not in inclusion: inclusion.append(k)
			if flb-subobj[k]+cost>max_inclusion_list[k] and subobj[k]<0: max_inclusion_list[k]=flb-subobj[k]+cost #???
		for i in range (num_districts):
			if i>=nf:
				k=objlist[i][0]
				subobj[k]=0.0
				yj[k]=0
				xij[k]=[0.0 for x in range(num_units)]

		for i in range(num_units):
			g=1.0
			for k in range(num_districts):
				g-=xij[k][i]
			gi[i]=g
		#flb=sum(subobj)+sum(multiplier)
		norm=sum(gi[x]*gi[x] for x in range(num_units))
		total_supply=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
		if total_supply>=total_pop-0.00001:
			best_lb_list.append([norm,yj[:],copy.deepcopy(xij)])
			best_lb_list.sort(key=lambda x: x[0])
			if len(best_lb_list)>10: del best_lb_list[-1]
		#print total_supply
		improved_lb+=1
		if flb>lb+0.0000001:
			lb=flb
			improved_lb=0
			d=sum(old_gi[x]*gi[x] for x in range(num_units))
		if improved_lb%10==9:
			alpha*=0.66
		cap=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
		cost=sum(facilityCost[x] for x in range(num_districts) if yj[x]==1)
		if (improved_lb==0 or improved_lb%20==0) and loop>=20:
			if improved_lb==0:
				upper_bound_CKFLP(yj,xij)
			else:
				if len(best_lb_list)>0:
					r=random.random()
					idx=int(r*r*0.999*len(best_lb_list))
					idx=0
					upper_bound_CKFLP(best_lb_list[idx][1],best_lb_list[idx][2])
					del best_lb_list[idx]
			all_solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
			fub=biobjective
			nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
			cap=sum(facilityCapacity[x] for x in range(num_districts) if yj[x]==1)
			cost=sum(facilityCost[x] for x in range(num_districts) if yj[x]==1)
			improved_ub+=1
			if fub<ub:
				ub=fub
				unf=nf
				alpha*=1.1
				improved_ub=0
		#update multiplier  
		sq=sum(x*x for x in gi)
		if abs(sq)<0.001:
			break
		t=alpha*(ub-flb)/sq
		for i in range(num_units):
			multiplier[i]+=t*gi[i]
			if multiplier[i]<0.0:
				multiplier[i]=0.0
		viol=sum(1 for x in gi if abs(x)>0.5)
		s=str(loop)+" bestub: "+str(unf)+" "+str(int(ub)) + " ub: "+str(int(fub))
		s+=" bestlb: " +str(int(lb)) + " lb: " +str(sum(yj))+" " +str(int(flb)) + " " +str(len(exclusion)) + " "+str(len(inclusion))
		#s+=" bestlb: " +str(int(lb)) + " lb: " +str(sum(yj))+" "+str(viol)+" " + str(int(norm))+" "
		#s+=str(int(flb)) +" "+ str(cap)+" " +str(int(alpha*100000)/100000.0) +" "+str(len(exclusion))
		arcpy_print(s)
		if abs(lb-ub)/ub<delta1:
			break
		if improved_lb+improved_ub>=loops: 
			break
	all_solutions.sort(key=lambda x:x[3]+x[4]+x[5]*2*avg_dis_min+x[6]*penalty_on_demand)
	#all_solutions.sort(key=lambda x:x[0])
	all_solutions=pop_selection(all_solutions)
	while len(all_solutions)>multi_start_count*2: all_solutions.pop()
	#while len(all_solutions)>5: all_solutions.pop()
	#spatial_contiguity=spatial_contiguity_tmp
	#print "max_exclusion_list",max_exclusion_list
	#print "max_inclusion_list",max_inclusion_list
def upper_bound_ap(xijlist):
	global node_groups
	global all_solutions
	global district_info
	node_groups=[-1 for x in range(num_units)]
	for k in range(num_districts):
		district_info[k][1]=0
	for i in range(num_units):
		klist=[[x,nodedik[i][x]] for x in range(num_districts) if xijlist[x][i] > 0.99] #0.66
		if len(klist)==0: continue
		klist.sort(key=lambda x: x[1])
		k=klist[0][0]
		node_groups[i]=k
		district_info[k][1]+=nodes[i][3]
	#ulist=[[x,nodes[x][3]] for x in range(num_units) if node_groups[x]==-1]
	#ulist.sort(key=lambda x: -x[1])
	#for x in ulist:
	#    i=x[0]
	#    for k in NearFacilityList[i]:
	#        if nodes[i][3]+district_info[k][1]<=facilityCapacity[k]:
	#            node_groups[i]=k
	#            district_info[k][1]+=nodes[i][3]
	#            break
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	for i in ulist:
		idx=0
		k=NearFacilityList[i][idx]
		node_groups[i]=k
	update_district_info()
	VND_local_search()
	return biobjective

def AP_LR_main(loops,gap_ul, gap_viol):
	global node_groups
	global centersID
	global multiplier
	global yj
	global xij
	global subobj
	global all_solutions
	global yj_possibility
	global xij_possibility
	global best_yj
	global best_xij
	global spatial_contiguity
	
	spatial_contiguity_tmp=spatial_contiguity
	spatial_contiguity=0
	xijlist=[]
	all_solutions=[]
	multiplier=[min(x)*(5+random.random())/5 for x in nodedik]
	subobj=[0.0 for x in range(num_districts)]
	xij=[[] for x in range(num_districts)]
	gi=[1.0 for  x in range(num_units)]
	gi_possibility=gi[:]
	ub=sum(max(x) for x in nodedik)
	unf=num_districts
	fub=ub
	lb=-MAXNUMBER
	delta1=0.001
	delta2=0.01
	alpha=1.0
	old_multiplier=multiplier[:]
	best_xij=copy.deepcopy(xij)
	best_multiplier=multiplier[:]
	improved_lb=0
	improved_ub=0
	for loop in range(loops):
		#search lower bound
		old_multiplier=multiplier[:]
		old_gi=gi[:]
		rlist=[]
		for k in range(num_districts):
			obj,y,xi=sub_CFLP_LR(k)
			subobj[k]=obj
			xij[k]=xi[:]
		flb=sum(subobj)+sum(multiplier)
		for i in range(num_units):
			g=1.0
			for k in range(num_districts):
				g-=xij[k][i]
			gi[i]=g
		
		improved_lb+=1
		if flb>lb+0.0000001:
			lb=flb
			improved_lb=0
			best_xij=copy.deepcopy(xij)
			best_multiplier=multiplier[:]

			d=sum(old_gi[x]*gi[x] for x in range(num_units))
			dm=sum(abs(old_multiplier[x]-multiplier[x]) for x in range(num_units))
			if d>=0.0:# or dm<sum(multiplier)*0.01:
				alpha*=1.1
				#if alpha>2: alpha=2.0
		if improved_lb%10==9:
			alpha*=0.66

		if improved_lb==0 or improved_lb%20==19 :
			upper_bound_ap(xij)
			all_solutions.append([biobjective,centersID[:],node_groups[:],0,0,0,0,0])
			fub=biobjective
			improved_ub+=1
			if fub<ub:
				ub=fub
				improved_ub=0
		sq=sum(x*x for x in gi)
		if abs(sq)<0.001:
			print "if abs(sq)<0.001"
			break
		t=alpha*(ub-flb)/sq
		for i in range(num_units):
			multiplier[i]+=t*gi[i]
		viol=sum(1 for x in gi if abs(x)>0.001)
		viol_pop=sum(nodes[x][3] for x in range(num_units) if abs(gi[x])>0.0001)
		s=str(loop)+" bestub: " +str(int(ub)) +" ub: "+str(int(fub))+" bestlb: "+str(int(lb))+" lb "+str(int(flb))
		arcpy_print(s)
		#print loop, "bestub",int(ub),"ub",int(fub),"bestlb",int(lb),"lb",int(flb),viol,viol_pop,int(alpha*100000)/100000.0
		#,gap_ul, gap_viol      
		if viol_pop<total_pop*gap_viol:
			print "viol_pop",viol_pop
			break
		if (ub-lb)/ub<gap_ul:
			print "gap_ul",gap_ul,(ub-lb)/ub
			break
		if improved_ub>=100: 
			print "improved_ub",improved_ub
			break
	all_solutions.sort(key=lambda x:x[0])
	spatial_contiguity=spatial_contiguity_tmp
	#while len(all_solutions)>=multi_start_count*2: all_solutions.pop()
	while len(all_solutions)>multi_start_count: all_solutions.pop()
	#for x in all_solutions: print x[0]
def sub_AP_LR(idx):
	udlist=[[i,(nodedik[i][idx]-multiplier[i])/nodes[i][3]] for i in range(num_units) if nodedik[i][idx]<= multiplier[i]]
	#udlist=[[i,(nodedik[i][idx]-multiplier[i])] for i in range(num_units) if nodedik[i][idx]<= multiplier[i]]
	udlist.sort(key=lambda x: x[1])
	demand=0
	xlist=[0.0 for i in range(num_units)]
	f=0.0
	for i in range(len(udlist)):
		u=udlist[i][0]
		if demand+nodes[u][3]<=facilityCapacity[idx]:
			demand+=nodes[u][3]
			f+=nodedik[u][idx]-multiplier[u]
			xlist[u]=1.0
		else:
			r=(facilityCapacity[idx]-demand)*1.0/nodes[u][3]
			f+=r*(nodedik[u][idx]-multiplier[u])
			xlist[u]=r
			break
	return f,1,xlist
	global node_groups
	global centersID
	global num_districts
	global district_info
	global all_solutions
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	for i in range(num_units):
		for j in range(num_districts):
			if flist[j]==1:
				xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
				costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]#-multiplier[i]

	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	prob += obj

	for i in range(num_units):
		s=""
		for j in range(num_districts):
			if flist[j]==1:
				s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1#nodes[i][3]

	#cons 3
	for k in range(num_districts):
		if flist[k]==0: continue
		s=""
		for i in range(num_units):
			s+=nodes[i][3] * xvariables["x_" +str(i)+ "_"+ str(k)]
		prob+=s <= facilityCapacity[k]

	#prob.writeLP("_location_LR.lp")
	gap=mipgap
	solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timelimit=maxtime, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	solver.actualSolve(prob)

	if prob.status<=0:
		return prob.status
	sol=[]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.50):
			items=v.name.split('_')
			i=int(items[1])
			k=int(items[2])
			node_groups[i]=k

	###noprint sol
	#num_districts=len(centersID)
	centersID=facilityCandidate[:]
	for k in range(num_districts):
		if flist[k]==0:
			centersID[k]=-1
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	update_district_info()
	return prob.status

def CFLP_CKFLP_model(numf,rand,maxtime,mipgap): #CFLP_CKFLP, i.e. split-demand 
	global node_groups
	global centersID
	global num_districts
	global district_info
	alpha_coeff=penalty_on_demand
	prob = pulp.LpProblem("location",pulp.LpMinimize)
	xvariables={}
	costs={}
	for i in range(num_units):
		for j in range(num_districts): 
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, None, pulp.LpInteger) #
			if rand==0:
				costs["x_" +str(i)+ "_"+ str(j)]=nodedik[i][j]/nodes[i][3]
			else:
				costs["x_" +str(i)+ "_"+ str(j)]=nodedik[i][j]/nodes[i][3] *(random.random()+49.5)/50
	yvariables={}
	for i in range(num_districts):
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		if rand==0:
			costs["y_" +str(i)]=facilityCost[i]
		else:
			costs["y_" +str(i)]=facilityCost[i]*(random.random()+49.5)/50
	obj=""
	for x in xvariables:
		obj += costs[x]*xvariables[x]
	if fixed_cost_obj==1:
		for y in yvariables:
			if costs[y]>0:
				obj += costs[y]*yvariables[y]
	#for x in hvariables:
	#    obj+=alpha_coeff*hvariables[x]
	prob +=obj


	s=""
	for k in range(num_districts):
		s+=yvariables["y_" +str(k)]
	if adaptive_number_of_facilities==0:
		prob +=s == numf
	#else:
	#    prob += s<=numf 
	
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == nodes[i][3]
	for i in range(num_units):
		for j in range(num_districts):
			s=xvariables["x_" +str(i)+ "_"+ str(j)] - nodes[i][3] *yvariables["y_" + str(j)]
			prob +=s <= 0

	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+=xvariables["x_" +str(i)+ "_"+ str(k)]
		#s-=hvariables["h_" +str(k)]
		s-=facilityCapacity[k]*(1+pop_deviation) * yvariables["y_" +str(k)]
		prob+=s <= 0
	s=""
	for k in range(num_districts): #for better relaxation only
		s+=facilityCapacity[k]*(1+pop_deviation)*yvariables["y_" +str(k)]
	prob+=s >= total_pop
	#selected supply unit must be assigned to itself
	#for k in range(num_districts):
	#    s=xvariables["x_" +str(facilityCandidate[k]) + "_"+ str(k) ] - nodes[facilityCandidate[k]][3]*yvariables["y_" +str(k)]
	#    prob+=s == 0
		
	#prob.writeLP("_location2.lp")
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,maxSeconds=maxtime,gapRel =mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, options=['set mip tolerances mipgap ' +str(mipgap)])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=maxtime,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		arcpy_print("MIP solver status: " + str(prob.status))
		return -1

	cid=[]
	sol=[[-1,-1] for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.50):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				cid.append(i)
				#print v,v.varValue
				continue
			if items[0]=="h": continue
			k=int(items[2])
			if v.varValue>sol[i][1]:
				sol[i][0]=k
				sol[i][1]=v.varValue
	
	centersID=facilityCandidate[:]
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	for k in range(num_districts):
		if k not in cid:
			centersID[k]=-1
	for i in range(num_units):
		node_groups[i]=sol[i][0]
	update_district_info()
	return prob.status

#build and solve a SAP model 
#build and solve a PDP model, when location_problem=2 
def SAP_model(): #SAP
	if mip_solver not in mip_solvers:
		return -2
##    if spatial_contiguity!=1:
##        sta=GAP_model(0,heuristic_time_limit/10,0.00001)
##        if sta<0:
##            return sta
##        update_district_info()
##        update_best_solution()
##        return sta
	global node_groups
	global centersID
	global district_info
	centers=centersID[:]
	maxflow=num_units
	alpha_coeff=penalty_on_demand
	prob = pulp.LpProblem("SAP",pulp.LpMinimize)
	yvariables={}
	ycosts={}
	for i in range(num_units):
		for k in range(num_districts):
			if centers[k]<0: continue
			yvariables["y_" +str(i)+ "_"+ str(k)]=pulp.LpVariable("y_" +str(i)+ "_"+ str(k), 0, None, pulp.LpBinary)
			ycosts["y_" +str(i)+ "_"+ str(k)]=nodedik[i][k]*travel_distance_weight
			d=nodedij[i][k]
			if envy_service_objective==1 and d>envy_service_distance:
				ycosts["y_" +str(i)+ "_"+ str(k)] +=envy_objective_weight*nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==10:
				ycosts["y_" +str(i)+ "_"+ str(k)] +=envy_objective_weight*nodes[i][3]*abs(d-envy_service_distance)
			if envy_service_objective==11:
				ycosts["y_" +str(i)+ "_"+ str(k)] +=envy_objective_weight*nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
			
	hvariables={}
	lvariables={}
	for k in range(num_districts):
		if centers[k]<0: continue
		hvariables["H_" + str(k)]=pulp.LpVariable("H_" +str(k), 0, None, pulp.LpContinuous)
		if location_problem==2:
			lvariables["L_" + str(k)]=pulp.LpVariable("L_" +str(k), 0, None, pulp.LpContinuous) 
	if spatial_contiguity==1:
		fvariables={}
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					if centers[k]<0: continue
					fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)
	obj=""
	for x in yvariables:
		obj += ycosts[x]*yvariables[x]
	if location_problem==2 or location_problem==0: #sap, pdp
		for x in hvariables:
			obj+=alpha_coeff*hvariables[x]
	if location_problem==2: #pdp
		for x in lvariables:
			obj+=alpha_coeff*lvariables[x]
	prob += obj

	for i in range(num_units):
		s=""
		for k in range(num_districts):
			if centers[k]<0: continue
			s+=yvariables["y_" +str(i)+ "_"+ str(k)]
		prob += s==1

	if location_problem==2 or location_problem==0: #sap, pdp
		for k in range(num_districts):
			if centers[k]<0: continue
			s=""
			for i in range(num_units):
				s+= nodes[i][3] * yvariables["y_" +str(i)+ "_"+ str(k)]
			if location_problem==0:
				s -= hvariables["H_"+str(k)]
				prob += s <= facilityCapacity[k]*(1+pop_deviation)
			if location_problem==2:
				#s -= hvariables["H_"+str(k)]
				prob += s-hvariables["H_"+str(k)] <= facilityCapacity[k]*(1+pop_deviation)
				prob += s+lvariables["L_"+str(k)] >= facilityCapacity[k]*(1-pop_deviation)

	if spatial_contiguity==1:
	#con 3
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					if centers[k]<0: continue
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= maxflow* yvariables["y_" +str(i)+ "_"+ str(k)]
					prob += s <= 0
	#con 4
		for i in range(num_units):
			for j in node_neighbors[i]:
				for k in range(num_districts):
					if centers[k]<0: continue
					s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
					s-= maxflow* yvariables["y_" +str(j)+ "_"+ str(k)]
					prob += s <= 0
	#con 5
		for i in range(num_units):
			if i in centersID: continue
			for k in range(num_districts):
				if centers[k]<0: continue
				s=""
				for j in node_neighbors[i]:
					s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
				s-= yvariables["y_" +str(i)+ "_"+ str(k)]
				prob += s >= 0
	#con 6
	if spatial_contiguity==1:    
		for k in range(num_districts):
			if centers[k]<0: continue
			s=yvariables["y_"+str(centers[k]) + "_" + str(k)]
			prob += s == 1
	mip_file="sap.lp"
	prob.writeLP(mip_file)
	
	'''initvalues=sap_mst()
	for x,v in initvalues:
		yvariables[x].setInitialValue(v)'''
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,maxSeconds=heuristic_time_limit,gapRel = 0.0000000000001,warmStart=True, options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=heuristic_time_limit,warmStart=True,options=['set mip tolerances mipgap 0.000000000001'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=heuristic_time_limit,warmStart=True,options=[("MIPGap",0.0000000000001),("TimeLimit",heuristic_time_limit)])
		#solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timelimit=heuristic_time_limit,options=['set mip tolerances mipgap 0.000000000001'])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	arcpy_print("solver status: " + pulp.LpStatus[prob.status])
	if prob.status<=0:
		return prob.status

	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				k=int(items[2])
				node_groups[i]=k
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	update_district_info()
	update_best_solution()
	return prob.status

def sap_mst():
	vars=[]
	if node_groups==[]: return vars
	for i in range(num_units):
		k=node_groups[i]
		v='y_'+str(i)+ '_'+ str(k)
		vars.append([v,1])
	return vars

def PDP_model(numf): #PDP
	if mip_solver not in mip_solvers:
		return -2
	global max_num_facility
	global heuristic_time_limit
	global avg_dis_min
	global district_info
	#initialize_instance()
	max_num_facility=numf
	if numf>=num_districts:
		arcpy_print("too large number of facilities to select!")
		arcpy_print("the demand units will be assigned to existing facilities!")
		max_num_facility=num_districts
	#sta=initial_solution(0)
	#if sta<0:
	#    return sta
	#update_district_info()
	#update_best_solution()
	global node_groups
	global centersID
	centers=facilityCandidate[:]
	if len(all_solutions)>=1: avg_dis_min=objective/total_pop
	alpha_coeff=penalty_on_demand
	f = open("pdp_gy2_10.lp","w")
	f.write("Minimize\nOBJ: ")
	for i in range(num_units):
		for k in range(num_districts):
			if centers[k]<0: continue
			s=str(nodedik[i][k]) + " x_" +str(i)+ "_"+ str(k)
			if i==num_units-1 and k==num_districts-1: 
				f.write(s+"\n")
			else:
				f.write(s+" + ")

	f.write("Subject To\n")
	cidx=0
	for i in range(num_units):
		s= "_c" + str(cidx) + ": "
		cidx+=1
		for k in range(num_districts):
			s+="x_" +str(i)+ "_"+ str(k)
			if k==num_districts-1:
				s+= " =1\n"
			else:
				s+= " + "
		f.write(s)

	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+= str(nodes[i][3]) + " x_" +str(i)+ "_"+ str(k)
			if i==num_units-1: break
			s+= " + "
		f.write("_c" + str(cidx) + ": ")
		cidx+=1
		s1=s + " - " + str((1+pop_deviation)*total_pop/max_num_facility) + " " + "y_" +str(k) + " <= 0\n"
		f.write(s1)
		f.write("_c" + str(cidx) + ": ")
		cidx+=1
		s1=s + " - " + str((1-pop_deviation)*total_pop/max_num_facility) + " " + "y_" +str(k) + " >= 0\n"
		f.write(s1)

	#for H L =0
	for i in range(num_units):
		for k in range(num_districts):
			s= "_c" + str(cidx) + ": "
			cidx+=1
			s+="x_" +str(i)+ "_"+ str(k) + "-10000 " + "y_" +str(k) + " <= 0\n"
			f.write(s)
	s= "_c" + str(cidx) + ": "
	cidx+=1
	for k in range(num_districts):
		s += "y_" +str(k)
		if k==num_districts-1:
		   s+= " = " +str(numf) +"\n"
		else:
		   s+= " + "
	f.write(s)

	for k in range(num_districts):
		s= "_c" + str(cidx) + ": "
		cidx+=1
		s+="x_"+ str(centers[k]) + "_" + str(k) + " - y_" +str(k) + " = 0\n"
		f.write(s)

	#con 3
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(num_districts):
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + " - "+ str(num_units-numf) + " x_" +str(i)+ "_"+ str(k) + " <= 0\n"
				f.write(s)
	#con 4
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(num_districts):
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + " - " +str(num_units-numf) + " x_" +str(j)+ "_"+ str(k) + " <= 0\n"
				f.write(s)
	#con 5
	for i in range(num_units):
		for k in range(num_districts):
			if centers[k]!=i:
				s= "_c" + str(cidx) + ": "
				cidx+=1
				for j in node_neighbors[i]:
					s+= "f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + " - f_" +str(j)+ "_"+str(i)+ "_"+ str(k) + " + "
				s=s[:-2]
				s +=  " - x_" +str(i)+ "_"+ str(k) + " >=0 \n"
				f.write(s)
	f.write("binaries\n")    
	for i in range(num_units):
		for k in range(num_districts):
			s="x_" +str(i)+ "_"+ str(k)+ "\n"
			f.write(s)    
	for k in range(num_districts):
		s="y_" + str(k)+ "\n"
		f.write(s)    
	f.write("generals\n")    
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(num_districts):
				s="f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + "\n"
				f.write(s)
	f.write("end\n")
	f.close()

def PDP2_model(numf): #Tong
	if mip_solver not in mip_solvers:
		return -2
	global max_num_facility
	global heuristic_time_limit
	global avg_dis_min
	global district_info
	#initialize_instance()
	max_num_facility=numf
	if numf>=num_districts:
		arcpy_print("too large number of facilities to select!")
		arcpy_print("the demand units will be assigned to existing facilities!")
		max_num_facility=num_districts
	centers=facilityCandidate[:]
	if len(all_solutions)>=1: avg_dis_min=objective/total_pop
	alpha_coeff=penalty_on_demand
	f = open("pdp"+str(numf)+".lp","w")
	f.write("Minimize\nOBJ: ")
	#for i in range(num_units):
	#    for k in range(num_districts):
	#        if centers[k]<0: continue
	#        s=str(nodedik[i][k]) + " x_" +str(i)+ "_"+ str(k)
	#        if i==num_units-1 and k==num_districts-1: 
	#            f.write(s+"\n")
	#        else:
	#            f.write(s+" + ")
	for i in range(num_units):
		for j in range(num_units):
			if i==j: continue
			for k in range(numf):
				s=str(nodedik[i][j]) + " z_" +str(i)+ "_" + str(j) + "_" + str(k) 
				if i==num_units-1 and j==num_units-2 and k==numf-1:
					f.write(s+"")
				else:
					f.write(s+" + ")
	f.write("\nSubject To\n")
	cidx=0
	for i in range(num_units):
		for j in range(num_units):
			if i==j: continue
			for k in range(numf):
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="z_" +str(i)+ "_"+ str(j)+ "_"+ str(k) + " - x_" +str(i)+ "_"+ str(k) + " - x_" +str(j)+ "_"+ str(k) + " >= -1\n"
				f.write(s)

	for i in range(num_units):
		for j in range(num_units):
			if i==j: continue
			for k in range(numf):
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="z_" +str(i)+ "_"+ str(j)+ "_"+ str(k) +  " - x_" +str(i)+ "_"+ str(k) + " <= 0\n"
				f.write(s)
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="z_" +str(i)+ "_"+ str(j)+ "_"+ str(k) +  " - x_" +str(j)+ "_"+ str(k) + " <= 0\n"
				f.write(s)

	for i in range(num_units):
		s= "_c" + str(cidx) + ": "
		cidx+=1
		for k in range(numf):
			s+="x_" +str(i)+ "_"+ str(k)
			if k==numf-1:
				s+= " =1\n"
			else:
				s+= " + "
		f.write(s)

	for k in range(numf):
		s=""
		for i in range(num_units):
			s+= str(nodes[i][3]) + " x_" +str(i)+ "_"+ str(k)
			if i==num_units-1: break
			s+= " + "
		f.write("_c" + str(cidx) + ": ")
		cidx+=1
		s1=s + " <= " + str((1+pop_deviation)*total_pop/max_num_facility) + "\n"
		f.write(s1)
		f.write("_c" + str(cidx) + ": ")
		cidx+=1
		s1=s + " >= " + str((1-pop_deviation)*total_pop/max_num_facility) + "\n"
		f.write(s1)

	for i in range(num_units):
		for k in range(numf):
			s= "_c" + str(cidx) + ": "
			cidx+=1
			s+="x_" +str(i)+ "_"+ str(k) + " - y_" +str(i)+ "_"+str(k) + " >= 0\n"
			f.write(s)

	for k in range(numf):
		s= "_c" + str(cidx) + ": "
		cidx+=1
		for i in range(num_units):
			s += "y_"+str(i)+ "_" +str(k)
			if i==num_units-1:
			   s+= " = 1\n"
			else:
			   s+= " + "
		f.write(s)

	#con 3
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(numf):
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + " - "+ str(num_units-numf) + " x_" +str(i)+ "_"+ str(k) + " <= 0\n"
				f.write(s)
	#con 4
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(numf):
				s= "_c" + str(cidx) + ": "
				cidx+=1
				s+="f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + " - " +str(num_units-numf) + " x_" +str(j)+ "_"+ str(k) + " <= 0\n"
				f.write(s)
	#con 5
	for i in range(num_units):
		for k in range(numf):
			s= "_c" + str(cidx) + ": "
			cidx+=1
			for j in node_neighbors[i]:
				s+= "f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + " - f_" +str(j)+ "_"+str(i)+ "_"+ str(k) + " + "
			s=s[:-2]
			s +=  " - x_" +str(i)+ "_"+ str(k) + " + "+str(num_units-numf+1) + "y_" +str(i)+ "_"+ str(k) +" >=0 \n"
			f.write(s)
	f.write("binaries\n")    
	for i in range(num_units):
		for k in range(numf):
			s="x_" +str(i)+ "_"+ str(k)+ "\n"
			f.write(s)    
	for i in range(num_units):
		for k in range(numf):
			s="y_" +str(i)+ "_"+ str(k)+ "\n"
			f.write(s)
	for i in range(num_units):
		for j in range(num_units):
			if i==j: continue
			for k in range(numf):
				s="z_" +str(i)+ "_"+ str(j)+ "_"+ str(k)+ "\n"
				f.write(s)
	f.write("generals\n")    
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(numf):
				s="f_" +str(i)+ "_"+str(j)+ "_"+ str(k) + "\n"
				f.write(s)
	f.write("end\n")
	f.close()

def CFLSAP_model(numf): #FL & SAP
	if mip_solver not in mip_solvers:
		return -2
	global max_num_facility
	global heuristic_time_limit
	global avg_dis_min
	global district_info
	#initialize_instance()
	max_num_facility=numf
	if numf>=num_districts:
		arcpy_print("too large number of facilities to select!")
		arcpy_print("the demand units will be assigned to existing facilities!")
		max_num_facility=num_districts
	#sta=initial_solution(0)
	#if sta<0:
	#    return sta
	#update_district_info()
	#update_best_solution()
	global node_groups
	global centersID
	centers=facilityCandidate[:]
	alpha_coeff=penalty_on_demand
	prob = pulp.LpProblem("LA-SAP",pulp.LpMinimize)
	yvariables={}
	zvariables={}
	ycosts={}
	zcost={}
	for i in range(num_units):
		for k in range(num_districts):
			if centers[k]<0: continue
			yvariables["y_" +str(i)+ "_"+ str(k)]=pulp.LpVariable("y_" +str(i)+ "_"+ str(k), 0, 1, pulp.LpBinary)
			ycosts["y_" +str(i)+ "_"+ str(k)]=nodedik[i][k]
	hvariables={}
	for k in range(num_districts):
		hvariables["H_" + str(k)]=pulp.LpVariable("H_" +str(k), 0, None, pulp.LpContinuous)
		if location_problem==2:
			hvariables["L_" + str(k)]=pulp.LpVariable("L_" +str(k), 0, None, pulp.LpContinuous)

		zvariables["z_" + str(k)]=pulp.LpVariable("z_" +str(k), 0, 1, pulp.LpBinary)
		if fixed_cost_obj==1:
			zcost["z_" + str(k)]=facilityCost[k]
	fvariables={}
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(num_districts):
				#if centers[k]<0: continue
				fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]=pulp.LpVariable("f_" +str(i)+ "_"+ str(j)+ "_"+ str(k), 0, None, pulp.LpInteger)
	obj=""
	for x in yvariables:
		obj += ycosts[x]*yvariables[x]
	for x in hvariables:
		obj+=alpha_coeff*hvariables[x]
	if fixed_cost_obj==1:
		for x in zvariables:
			if zcost[x]>0.0:
				obj+=zcost[x]*zvariables[x]
	prob += obj

	#assign
	for i in range(num_units):
		s=""
		for k in range(num_districts):
			s+=yvariables["y_" +str(i)+ "_"+ str(k)]
		prob += s==1
	#capacity
	for k in range(num_districts):
		s=""
		for i in range(num_units):
			s+= nodes[i][3] * yvariables["y_" +str(i)+ "_"+ str(k)]
		s1 = s - hvariables["H_"+str(k)]
		s1 -= facilityCapacity[k] * (1+pop_deviation)*zvariables["z_" +str(k)] 
		prob += s1 <= 0
		if location_problem==2:
		   s1 = s + hvariables["L_"+str(k)]
		   s1 -= facilityCapacity[k] *(1-pop_deviation)* zvariables["z_" +str(k)]
		   prob += s1 >= 0
	#for H L =0
	for i in range(num_units):
		for k in range(num_districts):
			s=yvariables["y_" +str(i)+ "_"+ str(k)]-10000*zvariables["z_" +str(k)]
			prob += s <= 0
	#can be removed
	#for k in range(num_districts):
	#    s=hvariables["H_" + str(k)]-10000*zvariables["z_" +str(k)]
	#    prob += s <= 0
	#    if location_problem==2:
	#        s=hvariables["L_" + str(k)]-10000*zvariables["z_" +str(k)]
	#        prob += s <= 0

	#K locations
	s=""
	for k in range(num_districts):
		s += zvariables["z_" +str(k)]
	if adaptive_number_of_facilities==0:
		prob += s == numf

	for k in range(num_districts):
		s=yvariables["y_"+str(centers[k]) + "_" + str(k)] - zvariables["z_" +str(k)]
		prob += s == 0

	#con 3
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(num_districts):
				s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
				s-= (num_units-numf)* yvariables["y_" +str(i)+ "_"+ str(k)]
				prob += s <= 0
	#con 4
	for i in range(num_units):
		for j in node_neighbors[i]:
			for k in range(num_districts):
				s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
				s-= (num_units-numf)* yvariables["y_" +str(j)+ "_"+ str(k)]
				prob += s <= 0
	#con 5
	for i in range(num_units):
		for k in range(num_districts):
			if centers[k]!=i:
				s=""
				for j in node_neighbors[i]:
					s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
				s-= yvariables["y_" +str(i)+ "_"+ str(k)]
				prob += s >= 0
			#else:
			#   for j in node_neighbors[i]:
			#        s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)]
			#        prob += s == 0


	#con 6
	# for k in range(num_districts):
		# i = centersID[k]   
		# for j in node_neighbors[i]:
			# s=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] + (num_units-num_districts)* zvariables["z_" +str(k)]
			# prob += s <= num_units-num_districts

	# for k in range(num_districts):
		# i = centersID[k]
		# s=""
		# for j in node_neighbors[i]:
			# s+=fvariables["f_" +str(i)+ "_"+str(j)+ "_"+ str(k)] - fvariables["f_" +str(j)+ "_"+str(i)+ "_"+ str(k)]
		# s+= (num_units-num_districts)* zvariables["z_" + str(k)]
		# prob += s >= 1

	#if location_problem==2:
	#    cid=[]
	#    for x in all_solutions: cid+=x[1]
	#    cid=list(set(cid))
	#    cid.remove(-1)
	#    for x in range(num_districts): 
	#        if x in cid: continue
	#        s=zvariables["z_" +str(x)]
	#        prob += s==0


	initvalues=CFLSAP_mst()
	for x,v in initvalues:
		if x.find("z")==0: 
			zvariables[x].setInitialValue(v)
		if x.find("y")==0: 
			yvariables[x].setInitialValue(v)
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,maxSeconds=heuristic_time_limit,gapRel = 0.0000000000001, warmStart=True,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=heuristic_time_limit,warmStart=True,options=[ 'set mip tolerances mipgap 0.000000000005', 'set parallel -1','set emphasis MIP 3'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,timeLimit=heuristic_time_limit,warmStart=True,options=[("MIPGap",0.00000000000001),("TimeLimit",heuristic_time_limit)])
	solver.setTmpDir() #=mip_file_path #'set threads 4',
	solver.actualSolve(prob)
	arcpy_print("solver status: " + pulp.LpStatus[prob.status])
	if prob.status<=0:
		return prob.status
	cid=[]
	node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				k=int(items[2])
				node_groups[i]=k
			if items[0]=='z':
				k=int(items[1])
				cid.append(k)
	centersID=facilityCandidate[:]
	for k in range(num_districts):
		if k not in cid:
			centersID[k]=-1
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	update_district_info()
	update_best_solution()
	return prob.status

def CFLSAP_mst():
	vars=[]
	if node_groups==[]: return vars
	for k in range(num_districts):
		v='z_'+ str(k)
		if k in node_groups:
			vars.append([v,1])
		else:
			vars.append([v,0])
	for i in range(num_units):
		for k in range(num_districts):
			v='y_'+str(i)+ '_'+ str(k)
			if k==node_groups[i]: 
				vars.append([v,1])
			else:
				vars.append([v,0])
	return vars

def mip(numf,problem_type,contiguity,timelimit):
#numf: for CKFLP, PMP only
#problem_type: 0 SAP/GAP, 1 Location Problems, 2 PDP (reserved)
#contiguity:-1 split, 0 non-contiguity, 1 contiguity
	global heuristic_time_limit
	global max_num_facility
	global spatial_contiguity
	global num_districts
	global facilityCandidate
	global nodedij
	global nodedik
	global node_groups
	global centersID
	global all_solutions
	global facilityCost
	spatial_contiguity=contiguity
	initialize_instance()
	max_num_facility=numf
	heuristic_time_limit=timelimit
	sta=0
	if problem_type==0 and contiguity==0: #GAP
		sta=GAP_model(0,heuristic_time_limit,0.000000001) 
	if problem_type==0 and contiguity==1: #SAP
		#sta=GAP_model(1,heuristic_time_limit,0.005)
		#repair_fragmented_solution()
		#VND_local_search()
		#ils(max_num_facility,multi_start_count,heuristic_time_limit,1, -1)
		multi_exchange(max_num_facility,multi_start_count,heuristic_time_limit,-1)
		sta=SAP_model() 
	if problem_type==1 and contiguity==0: #SSCFLP,SSCKFLP
		#LR_main(1000)
		cost_multipler=10
		#for i in range(num_districts): facilityCost[i]*=cost_multipler
		#multi_exchange(max_num_facility,multi_start_count,heuristic_time_limit,-1)
		sta=SSCFLP_SSCKFLP_model(max_num_facility,numf,heuristic_time_limit, 0.0000000001)
		#check solution
		nearlist=[-1 for x in range(num_units)]
		s="facility nearest index: "
		for i in range(num_units):
			k=node_groups[i]
			idx=NearFacilityList[i].index(k)
			nearlist[i]=idx
			s+=str(idx)+" "
		arcpy_print(s)
		s= "max: "+str(max(nearlist)) +" average: "+ str(sum(nearlist)*1.0/num_units)
		arcpy_print(s)
		not_opt_cands=[]
		s="facilities must excludeded in optimal solution: "
		for k in range(num_districts): 
			if max_exclusion_list[k] >biobjective+0.0000001:
				not_opt_cands.append(k)
				s+=str(k)+ " "
		arcpy_print(s)
		must_opt_cands=[]
		s="facilities must includeded in optimal solution: "
		for k in range(num_districts): 
			if max_inclusion_list[k] >biobjective+0.0000001:
				must_opt_cands.append(k)
				s+=str(k)+ " "
		arcpy_print(s)

		s="index of optimal facilities in exclusion_list: "
		clist=[[x,max_exclusion_list[x]] for x in range(num_districts)]
		clist.sort(key=lambda x: x[1])
		clist=[x[0] for x in clist]
		idxlist=[]
		for i in range(num_districts):
			k =centersID[i]
			if k <0: continue
			idx=clist.index(i)
			idxlist.append(idx)
		idxlist.sort()
		s+= str(idxlist)
		arcpy_print(s)

		s="index of optimal facilities in inclusion_list: "
		clist=[[x,max_inclusion_list[x]] for x in range(num_districts)]
		clist.sort(key=lambda x: -x[1])
		clist=[x[0] for x in clist]
		idxlist=[]
		for i in range(num_districts):
			k =centersID[i]
			if k <0: continue
			idx=clist.index(i)
			idxlist.append(idx)
		idxlist.sort()
		s+= str(idxlist)
		arcpy_print(s)
	if problem_type==1 and contiguity==1: #CKFLP,SSCFLP with contiguity
		#if mip_solver=="cplex" or mip_solver=="cbc" :
		#multi_exchange(numf,multi_start_count,heuristic_time_limit,-1)
		sta=CFLSAP_model(max_num_facility)
	if problem_type==2: #PDP
		multi_exchange(numf,multi_start_count,heuristic_time_limit,-1)
		if num_districts>=500 and num_units==len(facilityCandidate):
			cid=[]
			for x in all_solutions:
				cid+=[y for y in x[1] if y>=0]
			cid=list(set(cid))
			flist=cid[:]
			for x in cid:
				flist+=node_neighbors[x]
			flist=list(set(flist))
			flist.sort()
			facilityCandidate=flist
			for idx in range(num_districts): 
			   k=num_districts-idx-1
			   if k in flist: continue
			   for i in range(num_units):
				   del nodedij[i][k]
				   del nodedik[i][k]
			num_districts=len(flist)
			for i in range(num_units):
				k=node_groups[i]
				node_groups[i]=flist.index(k)
			s="selected facility centers: "+str(num_districts)
			arcpy_print(s)
		sta=CFLSAP_model(max_num_facility)
	if problem_type==3 and contiguity==0: #pmp (m=n)
		sta=pmp_model(numf,heuristic_time_limit,0.0000000001)
		#sta=check_solution_continuality_feasibility(node_groups)
		#print "Areal continuality(1 yes, 0 no):",sta
	if problem_type==3 and contiguity>=1: #pmp (m=n)
		ils_pmp(numf,multi_start_count,heuristic_time_limit,-1)
		# cid=centersID[:]
		# cid=list(set(cid))
		# cid.remove(-1)
		# centersID=cid[:]
		# facilityCandidate=cid
		# flist=cid
		# for idx in range(num_districts): 
			# k=num_districts-idx-1
			# if k in flist: continue
			# for i in range(num_units):
				# del nodedij[i][k]
				# del nodedik[i][k]
		# num_districts=len(flist)
		# for i in range(num_units):
			# k=node_groups[i]
			# node_groups[i]=flist.index(k)
		# print "facilityCandidate",facilityCandidate
		# print "node_groups", set(node_groups)
		sta=CFLSAP_model(max_num_facility) 
	if sta<=0:
		return "model unsilved!"
	if spatial_contiguity==1:
		sta=check_solution_continuality_feasibility(node_groups)
		print "Areal continuality(1 yes, 0 no):",sta
		if sta<=0:
			arcpy_print("infeasible solution on continuality")
			return [-1,-1,-1,-1] #"infeasible solution on continuality"
	if -1 in node_groups:
		arcpy_print("some units are not assigned")
		return [-1,-1,-1,-1,[]]
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	if spatial_contiguity==1  and check_solution_continuality_feasibility(best_solution_global)==0:
		arcpy_print("infeasible solution on continuality!")
		return [-1,-1,-1,-1,[]] #"infeasible solution on continuality"
	if -1 in node_groups:
		arcpy_print("some units not assigned!")
		return [-1,-1,-1,-1,[]] #"infeasible solution on continuality"
	all_solutions.append([biobjective,centersID[:],node_groups[:]])
	all_solutions.sort(key=lambda x:x[0])
	if location_problem>=2 or spatial_contiguity==1:
		sta=check_solution_continuality_feasibility(node_groups)
		print "Areal continuality(1 yes, 0 no):",sta

	return [biobjective, objective, objective_overload, centersID, node_groups]

#ils for EDP，PDP ( location_problem=2)
#ils for SAP (location_problem=0)
def EDP_ils(numf):
	global node_groups
	global centersID
	global region_pool
	global pool_index
	global all_solutions
	global max_num_facility
	global best_biobjective_global   
	global location_problem
	initialize_instance() #use numf
	max_num_facility=numf
	region_pool=[]
	pool_index=[[] for x in range(num_districts)]
	solutions=[]
	all_solutions=[]
	t=time.time()
	t_begin=time.time()
	loops=multi_start_count
	best_biobjective_global=MAXNUMBER
	operators=assignment_operators_selected[:]
	#solutions=generate_initial_solution()
	not_improve=0
	not_improve_best=0
	loop=0
	print "pop_deviation:",pop_deviation
	for idx in range(multi_start_count):
		initial_solution(idx)
		VND_local_search()
		update_best_solution()
		update_region_pool_all()
		location_check(1)
		solutions.append([biobjective,centersID[:],node_groups[:],objective_overload,0])
		nf=sum(1 for x in range(num_districts) if solutions[0][1][x]>=0)
		s="initial solution "+str(idx)+": "+str(nf)+" "+" "+str(biobjective)+" "+str(objective)+" "+str(objective_overload)
		print s,"conn=",check_current_solution_continuality_feasibility()
		'''for k in range(num_districts):
			if centersID[k]<0: continue
			u=facilityCandidate[k]
			#print k,facilityCandidate[k],district_info[k],[x for x in range(num_units) if node_groups[x]==k],check_continuality_feasibility(node_groups,k)
			print k,facilityCandidate[k],node_groups[k],district_info[k],check_continuality_feasibility(node_groups,k)'''
	solutions.sort(key=lambda x:x[0])
	update_best_solution()
	while 1:
		loop+=1
		r=random.random()
		idx = int(min(multi_start_count,len(solutions))*pow(r,1.2))
		node_groups=solutions[idx][2][:]
		centersID=solutions[idx][1][:]
		update_district_info()
		old_obj=best_biobjective_global
		#location_check(2)

		location_sign=""
		location_sign=" {0:02d}".format(idx)
		ruin_idx=assign_ruin_recreate(-1)
		#location_check(3) #facility unit assigned to other facility in ruin-repair method!!! init——sol
		#VND_local_search()
		if location_problem==2:
			update_EDP_centers()
		VND_local_search()
		if location_problem==2:
			update_EDP_centers()
		update_best_solution()
		update_region_pool_all()
		#location_check(4)
		location_sign+=" R"+str(ruin_idx)+" {0:08d}".format(int(biobjective-old_obj))
		solutions.append([biobjective,centersID[:],node_groups[:],objective_overload,0])
		
		not_improve_best+=1
		if best_biobjective_global<old_obj-0.0000001:
			impp=((best_biobjective_global-old_obj)/biobjective)*1000 #-0.1%
			not_improve_best+=int(max_loops_solution_not_improved*impp)
			if not_improve_best<0: not_improve_best=0
		solutions.sort(key=lambda x:x[0])
		solutions=pop_selection(solutions)
		all_solutions=solutions
		nf=sum(1 for x in range(num_districts) if solutions[0][1][x]>=0)
		s="Loop "+str(loop) + location_sign +" best: " +str(nf)+" " +str(int(best_biobjective_global))+" "+str(best_overload_global)
		nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
		sidx=min(multi_start_count,len(solutions)/2)
		s+=" current: "+str(nf)+" "+str(int(biobjective))+" " +str(objective_overload)#+ " Pop" + str(len(solutions)) +": "+str(int(solutions[0][0])) + "-" + str(int(solutions[-1][0]))
		s+=" " + str(not_improve_best)+" "+ str(time.time()-t_begin)
		arcpy_print(s)
		if not_improve_best>max_loops_solution_not_improved: break
		if time.time()-t_begin > heuristic_time_limit:  break
		if stop_searching==1: break

	s= "ILS solution: "+str(best_biobjective_global)+" "+str(best_objective_global)+" "+str(best_overload_global)+" "+str(time.time()-t)
	arcpy_print(s)
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_district_info()
	t=time.time()
	update_region_pool_all()
	if is_spp_modeling>=1:
		t=time.time()
		if sppmodel(heuristic_time_limit,0.0001)>0:
			s="spp solution: "+ str(biobjective)+" "+str(objective) + " " +str(objective_overload) +" "+str(time.time()-t)
			arcpy_print(s)
			update_district_info()
			update_best_solution()
	solutions.append([biobjective,centersID[:],node_groups[:]])
	solutions.sort(key=lambda x:x[0])
	all_solutions=solutions

	if spatial_contiguity>=1:
		sta=check_solution_continuality_feasibility(best_solution_global)
		arcpy_print("solution on continuality (0 no, 1 yes) : "+str(sta))
		#return [-1,-1,-1,-1] #"infeasible solution on continuality"
	all_solutions=solutions

def General_AP_ILS():
	global nodedij
	global nodedik
	global node_groups
	global centersID
	global envy_service_objective
	global travel_distance_weight

	temp_envy=envy_service_objective
	temp_distance_weight=travel_distance_weight

	if envy_service_objective==1:   
		envy_service_objective=0    
		nodedij_org=copy.deepcopy(nodedij)
		nodedik_org=copy.deepcopy(nodedik)
		for i in range(num_units):
			for j in range(num_districts):
				d=nodedij[i][j]
				nodedij[i][j]=travel_distance_weight*d  + envy_objective_weight*max(0,d-envy_service_distance)*max(0,d-envy_service_distance)
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
		travel_distance_weight=1
	if initial_solution_method>=10:
		SAP_model()
	else:        
		SAP_ils()
	if temp_envy==1:
		travel_distance_weight=temp_distance_weight
		envy_service_objective=temp_envy
		nodedij=nodedij_org
		nodedik=nodedik_org
	node_groups=best_solution_global
	centersID=best_centersID_global
	update_district_info()
	update_cflpr_district_info()

def SAP_ils():
	global best_biobjective_global
	global biobjective
	global node_groups
	global centersID
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	initialize_instance()
	all_solutions=[]
	region_pool=[]
	t=time.time()
	ga_time=0.0
	best_biobjective_global = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]

	solutions=[] #all
	pool_index=[[] for x in range(num_districts)]
	t_ga=time.time()
	multi_start=0
	for idx in range(multi_start_count):
		initial_solution(idx)
		#VND_local_search()
		update_best_solution()
		update_region_pool_all()
		location_check(1)
		solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
		nf=sum(1 for x in range(num_districts) if solutions[0][1][x]>=0)
		if initial_solution_method==9: #LR
			for x in all_solutions: 
				solutions.append(copy.deepcopy(x))
			best_biobjective_global=MAXNUMBER
			break
		s="initial solution "+str(idx)+": "+str(nf)+" "+" "+str(biobjective)+" "+str(objective)+" "+str(objective_overload)
		print s,"conn=",check_current_solution_continuality_feasibility()
	solutions.sort(key=lambda x:x[0])
	all_solutions=solutions
	not_improved=0
	not_improved_global=0
	improved_time=time.time()
	loop=-1
	while 1:
		loop+=1
		r=random.random()
		sidx = int(min(multi_start_count-1,len(solutions))* pow(r,2)*0.999)
		r=random.random()
		node_groups=solutions[sidx][2][:]
		centersID=solutions[sidx][1][:]
		update_district_info()
		update_best_solution()
		not_improved_global+=1
		old_ids=centersID[:]
		obj=biobjective
		old_best=best_biobjective_global
		ruin_idx,sta=assign_ruin_recreate(-1)
		VND_local_search()
		update_best_solution()
		update_region_pool_all()
		solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
		s=""
		if biobjective<old_best-0.000001:  #0.1%
			s=" *"
			impp=((biobjective-old_best)/biobjective)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		elif biobjective<obj-0.0001: 
			s=" #"
		else: s=" -"

		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop)+str([ruin_idx])+" best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		nf=sum(1 for x in centersID if x>=0)
		s+=" current: " +str(int(solutions[sidx][0]))+" -> "+str(nf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_overload))

		n=num_districts 
		s+=" "+ str(n)
		surplus=int(objective_supply-total_pop)

		s+= " Info: " +str(not_improved_global)+ " "+str(int(time.time()-t_ga))
		arcpy_print(s)
		solutions.sort(key=lambda x:x[0])
		solutions=pop_selection(solutions)
		while len(solutions)>multi_start_count*2:
			solutions.pop()
		all_solutions=solutions
		if time.time()-t_ga > heuristic_time_limit:  break
		if not_improved_global >= max_loops_solution_not_improved: break
	#post procedure
	solutions.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #solutions[0][2][:]
	centersID=best_centersID_global[:]
	update_district_info()
	ga_time=time.time()-t_ga
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sppmodel(100,0.000001)
		update_district_info()
		update_best_solution()
		VND_local_search()
		solutions.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		print "spp solution:",biobjective,objective_fcost,objective,objective_overload,time.time()-t_spp, time.time()-t_spp
	print "final solution:",biobjective,objective_fcost,objective,objective_overload
	solutions.sort(key=lambda x:x[0])
	all_solutions=solutions

	sta=check_solution_continuality_feasibility(node_groups)
	print "Areal continuality(1 yes, 0 no):",sta
	if spatial_contiguity==1 and sta==0: 
		print "infeasible final solution: continuality"
		return "infeasible final solution: continuality"
	##noprint "time",time.time()-t
	return 
	
def vns(numf,popsize,timelimit,spp, sd):
	global seed
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global acceptanceRule
	global move_count
	global region_pool
	global pool_index
	global is_spp_modeling
	global all_solutions
	global best_solution
	global best_centersID
	global spatial_contiguity
	global facilityselected
	global num_districts
	global potential_facilities
	global max_num_facility
	global heuristic_time_limit
	global multi_start_count
	global is_spp_modeling
	global assignment_operators_selected
	max_num_facility=numf
	initialize_instance() #use numf
	if location_problem==0:
		max_num_facility=num_districts
	multi_start_count=popsize
	is_spp_modeling=spp
	seed=sd
	myseed=seed
	if seed<0:
		myseed=random.randint(0,100)
	random.seed(myseed)
	#print "seed",seed,myseed
	heuristic_time_limit=timelimit
	if mip_solver not in mip_solvers: is_spp_modeling=-1
	acceptanceRule="vns"
	region_pool=[]
	pool_index=[[] for x in range(num_districts)]
	solutions=[]
	all_solutions=[]
	t=time.time()
	move_count=0
	t_begin=time.time()
	#networkdij()
	#initial solutions as population
	ids=[]
	loops=multi_start_count
	best_biobjective_global=MAXNUMBER
	#assignment_operators_selected=[0,1]
	solutions=generate_initial_solution()
	all_solutions=solutions
	not_improve=0
	not_improve_best=0
   
	loop=0
	r_r_stat=[ [0,0,0,0,0,0] for i in range(6)]
	#ruin_list=[0,1,2,3,4]
	#if location_problem==0:    #5path relink
	#    ruin_list=[0,1,2,3,4,5]
	ruin_list=ruin_oprators
	while 1:
		loop+=1
		old_centersID=centersID[:]
		old_obj=biobjective
		r=random.random()
		idx = int(min(multi_start_count,len(solutions))*pow(r,2))
		#idx = int(len(solutions)*pow(r,2))
		node_groups=solutions[idx][2][:]
		centersID=solutions[idx][1][:]
		old_centersID=solutions[idx][1][:]
		update_district_info()
		update_best_solution()

		location_sign=""
		old_objective_overload=objective_overload
		location_sign=" {0:02d}".format(idx)+" L0 --------"
		ruin_idx=9

		if location_problem==1 and random.random()>0.5:
			old_obj=biobjective
			r_r_new_location(-1)
			update_district_info()
			update_best_solution()
			if old_centersID!=centersID:
				VND_local_search()
				update_region_pool_all()
			diff=sum(1 for x in range(num_districts) if centersID[x]!=old_centersID[x])            
			location_sign=" {0:02d}".format(idx)+" L"+str(diff)
			location_sign+=" "+ "{0:08d}".format(int(biobjective-old_obj)) #+"/"+"{0:08d}".format(int(save_est))
			location_sign+=" RX --------"
		#if objective_overload <= max (old_objective_overload, total_pop*0.001):
		else:
			old_obj=biobjective
			#ruin_idx=assign_ruin_recreate()
			#VND_local_search()
			VNS_local_search()
			if location_problem==2 or location_problem==3: 
				if all_units_as_candadate_locations==1: update_centers()
			update_best_solution()
			update_region_pool_all()
			#location_check(3)
			location_sign+=" R"+str(ruin_idx)+" {0:08d}".format(int(biobjective-old_obj))
		cost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		solutions.append([biobjective,centersID[:],node_groups[:],cost,objective_overload,0])
		not_improve_best+=1
		if biobjective<solutions[0][0]-0.0000001:
			not_improve_best=0

		solutions.sort(key=lambda x:x[0])
		solutions=pop_selection(solutions)
		all_solutions=solutions

		t2=time.time()-t_begin
		nf=sum(1 for x in range(num_districts) if solutions[0][1][x]>=0)
		supply=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)            
		s=acceptanceRule +" loop "+str(loop) + location_sign +" best: " +str(nf)+" " +str(int(best_biobjective_global))+" "+str(best_overload_global)
		nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
		sidx=min(multi_start_count,len(solutions)/2)
		s+=" current: "+str(nf)+" "+str(int(biobjective))+" " +str(objective_overload)+ " Pop" + str(len(solutions)) +": "+str(int(solutions[0][0])) + "-" + str(int(solutions[-1][0]))
		arcpy_print(s)
		if not_improve_best>max_loops_solution_not_improved: break
		if time.time()-t_begin > heuristic_time_limit:  break

	#for x in r_r_stat:
	#    print x[1],x[0],x[2],x[3]
	s= "ILS solution: "+str(best_biobjective_global)+" "+str(best_objective_global)+" "+str(best_overload_global)+" "+str(time.time()-t)
	arcpy_print(s)
	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_district_info()
	#if 1 not in assignment_operators_selected: assignment_operators_selected.append(1)
	#elif 2 not in assignment_operators_selected: assignment_operators_selected.append(2)
	t=time.time()
	#VND_local_search()
	#update_best_solution()
	#update_region_pool_all()
	#s="VND solution: "+ str(biobjective)+" "+str(objective) + " " +str(objective_overload) +" "+str(time.time()-t)
	#arcpy_print(s)
	update_region_pool_all()
	if is_spp_modeling>=1:
		t=time.time()
		if sppmodel(heuristic_time_limit,0.0001)>0:
			s="spp solution: "+ str(biobjective)+" "+str(objective) + " " +str(objective_overload) +" "+str(time.time()-t)
			arcpy_print(s)
			update_district_info()
			update_best_solution()
	solutions.append([biobjective,centersID[:],node_groups[:]])
	solutions.sort(key=lambda x:x[0])
	all_solutions=solutions

	if spatial_contiguity>=1:
		sta=check_solution_continuality_feasibility(best_solution_global)
		arcpy_print("solution on continuality (0 no, 1 yes) : "+str(sta))
		#return [-1,-1,-1,-1] #"infeasible solution on continuality"
	if -1 in best_solution_global:
		arcpy_print("some units are not assigned")
		return [-1,-1,-1,-1]
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	#s="solution check "+str(biobjective)+ " " + str(fcost)+" " +str(objective) +" " + str(objective_overload) + " " +str(biobjective-objective-fcost)
	#arcpy_print(s)
	search_stat()
	all_solutions=solutions
	return [best_biobjective_global, best_objective_global, best_overload_global, best_centersID_global, best_solution_global]
def spp_mst():
	vars=[]        
	num_pool=len(region_pool)
	for k in range(num_districts):
		ulist=[x for x in range(num_units) if node_groups[x]==k] 
		for i in range(num_pool):
			if ulist==region_pool[i][0] and region_pool[i][4]==k:
				vars.append([i,1])
				break
	return vars
def cflpr_scp_model(maxr2,maxr,cover_pecentage,maxtime,mipgap): #bug, the covering constraint
	global node_groups
	global centersID
	if len(region_pool)<=10:
		print "len(region_pool)<=10", len(region_pool)
		return 0
	penalty=penalty_on_demand
	prob = pulp.LpProblem("sdp_spp",pulp.LpMinimize)
	variables=[]
	costs=[]
	for i in range(len(region_pool)):
		x=pulp.LpVariable("x_" +str(i), 0, 1,pulp.LpBinary)
		variables.append(x)
		cost=region_pool[i][1]*travel_distance_weight+region_pool[i][3]*penalty 
		cost+=max(0,facilityMinimumCapacity-region_pool[i][2])*penalty       
		k=region_pool[i][4]
		if fixed_cost_obj==1: 
			cost+=facilityCost[k]
		if envy_service_objective==1:
			envyobj=0.0
			for j in region_pool[i][0]:
				d=nodedij[j][k]
				if d>envy_service_distance:
					envyobj+=nodes[j][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			cost+=envyobj
		if envy_service_objective==4:
			envyobj=0.0
			for j in region_pool[i][0]:
				d=nodedij[j][k]
				if d>envy_service_distance:
					envyobj+=nodes[j][3]*envy_objective_weight*(d-envy_service_distance)
			cost+=envyobj
		costs.append(cost)
	zvariables=[]
	for i in range(num_units):
		x=pulp.LpVariable("z_" +str(i), 0, 1,pulp.LpBinary)
		zvariables.append(x)
	obj=""
	for i in range(len(region_pool)):
		obj+=costs[i]*variables[i]
	prob+=obj

	for i in range(num_units):
		s=""
		for idx in range(len(region_pool)):
			if i in region_pool[idx][0]: 
				s+=variables[idx]
		if spatial_contiguity==0:
			prob+=s >= 1
		else:
			prob+=s == 1

	for i in range(num_units):
		s=""
		for idx in range(len(region_pool)):
			if i in region_pool[idx][0]: 
				k=region_pool[idx][4]
				if nodedij[i][k]<=maxr:s+=variables[idx]
		if spatial_contiguity==0:
			prob+=s- zvariables[i]>= 0
		else:
			prob+=s -zvariables[i] == 0

	for i in range(num_units):
		s=""
		for idx in range(len(region_pool)):
			if i in region_pool[idx][0]: 
				k=region_pool[idx][4]
				if nodedij[i][k]<=maxr2:
					s+=variables[idx]
		prob+= s >= 1

	if spatial_contiguity==0:
		for k in range(num_districts):
			s=""
			for i in range(len(region_pool)):
				if region_pool[i][4]!=k: continue
				s+=variables[i]
			if len(s)>1: prob+=s <= 1

	for k in range(num_districts):
		if k not in facility_inclusion_list: continue
		s=""
		for i in range(len(region_pool)):
			if region_pool[i][4]!=k: continue
			s+=variables[i]
		if len(s)>0: prob+=s == 1

	if adaptive_number_of_facilities==0:
		s=""
		for i in range(len(region_pool)):
			s+=variables[i]
		prob+=s == max_num_facility

	if max_facility_cost>0:
		s=""
		for i in range(len(region_pool)):
			k=region_pool[i][4]
			s+=facilityCost[k]*variables[i]
		prob+= s <= max_facility_cost

	s=""
	for i in range(num_units):
		s+=nodes[i][3]*zvariables[i]
	maxc=total_pop*cover_pecentage/100
	prob += s>=maxc

	prob.writeLP("_sclp.lp")
	#mip_mst_file=tempfile.mkstemp()[1].split("\\")[-1]

	vars=spp_mst()
	for x,v in vars: variables[x].setInitialValue(v)
	solver=0
	if mip_solver=='cbc': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.COIN_CMD(timeLimit=maxtime,mip=1,msg=solver_message,gapRel=mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,warmStart=True,timeLimit=maxtime,options=['set parallel -1','set mip tolerances mipgap ' + str(mipgap)])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	#if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
	if prob.status<=0:
	   print "no solution! prob.status=", prob.status
	   return prob.status #failer
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	for v in prob.variables():
		if (v.varValue >= 0.99):
			items=v.name.split('_')
			if items[0]!="x": continue
			i=int(items[1])
			k=region_pool[i][4]
			#print k,costs[i],facilityCost[k]
			centersID[k]=facilityCandidate[k]
			for x in region_pool[i][0]:
				node_groups[x]=k
	#a=[ x for x in centersID if x>=0]
	#print "spp locs:",len(a),a
	update_district_info()
	#for i in range(num_districts): 
	#    if district_info[i][1] >0: print i,district_info[i],facilityCost[i]
	#print 
	return 1 #success
	
def pcp_scp_model2(num_f,maxtime,mipgap): #bug, the covering constraint
	global node_groups
	global centersID
	if len(region_pool)<=10:
		print "len(region_pool)<=10", len(region_pool)
		return 0
	num_cands=len(region_pool)
	arcpy_print("SPP modelling..."+str(num_cands) ) 
	prob = pulp.LpProblem("sdp_spp",pulp.LpMinimize)
	variables=[]
	maxr=pulp.LpVariable("r", 0, None,pulp.LpContinuous)
	for i in range(num_cands):
		x=pulp.LpVariable("x_" +  str(i), 0, 1,pulp.LpBinary)
		variables.append(x)

	obj=maxr
	prob+=obj

	rlist=[[] for i in range(num_units)]
	for i in range(num_units):
		tlist=[]
		for j in range(num_cands):
			if i in region_pool[j][0]: tlist.append(j)
		rlist[i]=tlist[:]

	for i in range(num_units):
		#print i,rlist[i]
		s=""
		for x in rlist[i]:
			s+=variables[x]
		prob+=s >= 1

	
	for i in range(num_cands):
		r=max(nodedij[x][node_groups[x]] for x in region_pool[i][0])
		s=r*variables[i]-maxr
		prob += s<=0
		
	s=""
	for i in range(num_cands):
		s+=variables[i]
	prob+= s==num_f
	#prob.writeLP("_spp.lp")
	#mip_mst_file=tempfile.mkstemp()[1].split("\\")[-1]

	vars=spp_mst()
	for x,v in vars: variables[x].setInitialValue(v)
	solver=0
	if mip_solver=='cbc': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.COIN_CMD(timeLimit=maxtime,mip=1,msg=solver_message,gapRel=mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,warmStart=True,timeLimit=maxtime,options=['set parallel -1','set mip tolerances mipgap ' + str(mipgap)])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	#if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
	if prob.status<=0:
	   print "prob.status<0..."
	   return prob.status #failer
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	bestr=0.0
	for v in prob.variables():
		if v.name=="r": 
			bestr=v.varValue
			continue
		if (v.varValue >= 0.99):
			items=v.name.split('_')
			if items[0]!="x": continue
			i=int(items[1])
			k=region_pool[i][4]
			centersID[k]=facilityCandidate[k]
			for i in region_pool[i][0]:
				node_groups[i]=k
	update_district_info()
	obj_new=max(nodedij[x][node_groups[x]] for x in range(num_units))
	print "scp obj and maxr", bestr,obj_new
	return obj_new #success
	
def lscp_scp_model(maxr,cover_pecentage,maxtime,mipgap): #bug, the covering constraint
	global node_groups
	global centersID
	if len(region_pool)<=10:
		print "len(region_pool)<=10", len(region_pool)
		return 0
	klist=[x[4] for x in region_pool]
	klist=list(set(klist))
	arcpy_print("SPP modelling..."+str(len(klist)) ) 
	prob = pulp.LpProblem("sdp_spp",pulp.LpMinimize)
	variables={}
	for i in klist:
		x=pulp.LpVariable("x_" +"{0:07d}".format(i), 0, 1,pulp.LpBinary)
		variables[i]=x

	zvariables={}
	for i in range(num_units):
		x=pulp.LpVariable("z_" +"{0:07d}".format(i), 0, 1,pulp.LpBinary)
		zvariables[i]=x

	obj=""
	for x in klist:
		obj+=variables[x]
	prob+=obj

	rlist=[[] for i in range(num_units)]
	for i in range(num_units):
		tlist=[]
		for k in klist:
			if nodedij[i][k]<=maxr: tlist.append(k)
		rlist[i]=tlist[:]

	for i in range(num_units):
		s=""
		for x in rlist[i]:
			s+=variables[x]
		s-=zvariables[i]
		prob+=s >= 0

	s=""
	for i in range(num_units):
		s+=nodes[i][3]*zvariables[i]
	maxc=total_pop*cover_pecentage/100
	prob += s>=maxc
	
	#s=""
	#for i in range(len(region_pool)):
	#    if maxr_cover_list[i]>0:
	#        s+=maxr_cover_list[i]*variables[i]
	#if len(s)>1:
	#    maxc=total_pop - total_pop*cover_pecentage/100
	#    prob += s<=maxc
		
	if adaptive_number_of_facilities==0:
		s=""
		for i in range(len(variables)):
			s+=variables[i]
		prob+= s==max_num_facility
	#prob.writeLP("_spp.lp")
	#mip_mst_file=tempfile.mkstemp()[1].split("\\")[-1]

	#vars=spp_mst()
	#for x,v in vars: variables[x].setInitialValue(v)
	solver=0
	if mip_solver=='cbc': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.COIN_CMD(timeLimit=maxtime,mip=1,msg=solver_message,gapRel=mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,warmStart=False,timeLimit=maxtime,options=['set parallel -1','set mip tolerances mipgap ' + str(mipgap)])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=False,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	#if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
	if prob.status<=0:
	   print "prob.status<0..."
	   return prob.status #failer
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	for v in prob.variables():
		if (v.varValue >= 0.99):
			items=v.name.split('_')
			if items[0]=="z": continue
			k=int(items[1])
			centersID[k]=facilityCandidate[k]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	return 1 #success


def sppmodel(maxtime,mipgap):
	global node_groups
	global centersID
	if mip_solver not in mip_solvers:
		return 0
	if len(region_pool)<=10:
		##noprint "no candidate district!"
		print "len(region_pool)<=10", len(region_pool)
		return 0
	alpha_coeff=penalty_on_demand
	prob = pulp.LpProblem("_spp",pulp.LpMinimize)
	variables=[]
	costs=[]
	###noprint "buiding spp model..."
	#cost_stat=[]
	#cost_sum=[[0,0.0,0.0] for k in range(num_districts)]
	#for x in region_pool: print x
	for i in range(len(region_pool)):
		x=pulp.LpVariable("x_" +"{0:07d}".format(i), 0, 1,pulp.LpBinary)
		variables.append(x)
		cost=region_pool[i][1]*travel_distance_weight+region_pool[i][3]*alpha_coeff
		k=region_pool[i][4]
		#c2=sum(nodedik[x][k] for x in region_pool[i][0])
		#if abs(c2-cost)>0.001: print "check...", i,k,c2,cost,region_pool[i][1],region_pool[i][3]
		if fixed_cost_obj==1: ##[ulist,dis,demand,overload,k]
			cost+=facilityCost[k]
		if facilityMinimumCapacity>0:
			cost+=max(0,  facilityMinimumCapacity-region_pool[i][2]) *  alpha_coeff    
		if facilityMaximumCapacity>0:
			cost+=max(0,  region_pool[i][2] -facilityMaximumCapacity) *  alpha_coeff    
		if envy_service_objective==1:
			for j in region_pool[i][0]:
				if nodedij[j][k]>envy_service_distance:
					d=nodedij[j][k]-envy_service_distance
					cost+= nodes[j][3]* envy_objective_weight*d*d
		if envy_service_objective==4:
			for j in region_pool[i][0]:
				if nodedij[j][k]>envy_service_distance:
					d=nodedij[j][k]-envy_service_distance
					cost+= nodes[j][3]* envy_objective_weight*d
		costs.append(cost)
		#cost_stat.append(cost/region_pool[i][2])
		#cost_sum[k][0]+=1
		#cost_sum[k][1]+=cost/region_pool[i][2]
	#for k in range(num_districts):
	#    if cost_sum[k][0]>0:
	#        cost_sum[k][2]=cost_sum[k][1]/cost_sum[k][0]

	obj=""
	for i in range(len(region_pool)):
		obj+=costs[i]*variables[i]
	prob+=obj
	#for i in range(len(region_pool)):
	#    k=region_pool[i][4]
	#    if cost_stat[i]>cost_sum[k][2]:
	#        prob+= variables[i]==0
	#print region_pool
	#print costs
	rlist=[[] for i in range(num_units)]
	for j in range(len(region_pool)):
		for x in region_pool[j][0]:
			rlist[x].append(j)
	for i in range(num_units):
		s=""
		for x in rlist[i]:
			s+=variables[x]
		if spatial_contiguity>0: #2 edp
			prob+=s == 1
		else:
			prob+=s >= 1
	if spatial_contiguity==0:
		for k in range(num_districts):
			s=""
			for i in range(len(region_pool)):
				if region_pool[i][4]!=k: continue
				s+=variables[i]
			if len(s)>0: prob+=s <= 1

	if adaptive_number_of_facilities==0:
		s=""
		for i in range(len(variables)):
			s+=variables[i]
		prob+= s==max_num_facility
	if max_facility_cost>0:
		s=""
		for i in range(len(region_pool)):
			k=region_pool[i][4]
			s+=facilityCost[k]*variables[i]
		prob+= s <= max_facility_cost
	prob.writeLP("_spp.lp")
	#mip_mst_file=tempfile.mkstemp()[1].split("\\")[-1]

	vars=spp_mst()
	for x,v in vars: variables[x].setInitialValue(v)
	solver=0
	if mip_solver=='cbc': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.COIN_CMD(timeLimit=maxtime,mip=1,msg=solver_message,gapRel=mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,warmStart=True,timeLimit=maxtime,options=['set parallel -1','set mip tolerances mipgap ' + str(mipgap)])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	#if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
	if prob.status<=0:
	   print "prob.status<0..."
	   return prob.status #failer
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	for v in prob.variables():
		if (v.varValue >= 0.99):
			items=v.name.split('_')
			i=int(items[1])
			k=region_pool[i][4]
			#print k,costs[i],facilityCost[k]
			centersID[k]=facilityCandidate[k]
			for x in region_pool[i][0]:
				node_groups[x]=k
	a=[ x for x in centersID if x>=0]
	print "spp locs:",len(a),a
	update_district_info()
	#for i in range(num_districts): 
	#    if district_info[i][1] >0: print i,district_info[i],facilityCost[i]
	#print 
	return 1 #success
		
def GAP_model(rand,maxtime,mipgap): #GAP 
	global node_groups
	prob = pulp.LpProblem("init_sdp",pulp.LpMinimize)
	variables={}
	costs={}
	alpha_coeff=penalty_on_demand
	for i in range(num_units):
		for j in range(num_districts):
			if centersID[j]<0: continue
			variables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			cost=nodedik[i][j]
			if rand==1 or spatial_contiguity==1:
				cost*=(random.random()+29.5)/30
			costs["x_" +str(i)+ "_"+ str(j)]=cost
	hvariables={}
	for k in range(num_districts):
		if centersID[k]<0: continue
		hvariables["h_" +str(k)]=pulp.LpVariable("h_" +str(k), 0, None, pulp.LpInteger)

	obj=""
	for x in variables:
		obj += costs[x]*variables[x]
	for x in hvariables:
		obj += alpha_coeff*hvariables[x]
	prob +=obj
	if spatial_contiguity==1:
		for k in range(num_districts):
			if centersID[k]<0: continue
			s=variables["x_" +str(centersID[k])+ "_"+ str(k)]
			prob +=s == 1
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			if centersID[j]<0: continue
			s+=variables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == 1

	for k in range(num_districts):
		if centersID[k]<0: continue
		s=""
		for i in range(num_units):
			s+=nodes[i][3]*variables["x_" +str(i)+ "_"+ str(k)]
		s-=hvariables["h_" +str(k)]
		prob+=s <= facilityCapacity[k]
	#prob.writeLP("_gap.lp")
	solver=pulp.apis.COIN_CMD(mip=1,msg=0,timeLimit=maxtime,gapRel = mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	#prob.solve(solver=cbc)
	if mip_solver=="cplex":
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, options=['set mip tolerances mipgap '+ str(mipgap)])
		if rand==0:
			solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,timeLimit=maxtime, options=['set mip tolerances mipgap 0.0000000000001'])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	#arcpy_print("solver status: " + pulp.LpStatus[prob.status])
	if prob.status<=0:
		##noprint "model unsolved..."
		return prob.status
	sol=[]
	t=[]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			###noprint v,v.varValue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='h':
				t.append([i,v.varValue])
				continue
			k=int(items[2])
			sol.append([i,k])
	node_groups=[-1 for x in range(num_units)]
	for i in range(len(sol)):
		node_groups[sol[i][0]]=sol[i][1]
	update_district_info()
	return prob.status

def TP_model(rand):
	global node_groups
	prob = pulp.LpProblem("init_sdp",pulp.LpMinimize)
	variables={}
	costs={}
	alpha_coeff=penalty_on_demand
	for i in range(num_units):
		for j in range(num_districts):
			if centersID[j]<0: continue
			variables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, None, pulp.LpContinuous) #
			cost=nodedij[i][j] #*(random.random()+49.5)/50
			if rand==1:
				cost*=(random.random()+24.5)/25
			costs["x_" +str(i)+ "_"+ str(j)]=cost
	#hvariables={}
	#for i in range(num_districts):
	#    if centersID[i]<0: continue
	#    hvariables["h_" +str(i)]=pulp.LpVariable("h_" +str(i), 0, None, pulp.LpInteger)

	obj=""
	for x in variables:
		obj += costs[x]*variables[x]
	#for x in hvariables:
	#    obj += alpha_coeff*hvariables[x]
	prob +=obj

	if spatial_contiguity==1:
		for k in range(num_districts):
			if centersID[k]<0: continue
			s=variables["x_" +str(centersID[k])+ "_"+ str(k)]
			prob +=s == nodes[centersID[k]][3]
	for i in range(num_units):
		s=""
		for j in range(num_districts):
			if centersID[j]<0: continue
			s+=variables["x_" +str(i)+ "_"+ str(j)]
		prob +=s == nodes[i][3]

	for k in range(num_districts):
		if centersID[k]<0: continue
		s=""
		for i in range(num_units):
			s+=variables["x_" +str(i)+ "_"+ str(k)]
		#s-=hvariables["h_" +str(k)]
		prob+=s <= facilityCapacity[k]
	#prob.writeLP("_tp.lp")
	solver=pulp.apis.COIN_CMD(msg=0)
	if mip_solver=="cplex":
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=0)
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=0)
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return -1
	sol=[[-1,-1] for x in range(num_units)]
	sol2=[]
	for v in prob.variables():
		if (v.varValue >= 0.1):
			###noprint v,v.varValue
			items=v.name.split('_')
			if items[0]=="h": continue
			i=int(items[1])
			k=int(items[2])
			sol2.append([i,k,v.varValue])
			#print i,k,v.varValue,nodes[i][3]
			if v.varValue>sol[i][1]:
				sol[i][0]=k
				sol[i][1]=v.varValue
			
	node_groups=[x[0] for x in sol]
	update_district_info()
	#xij=[sol[i][1]*1.0/nodes[i][3] for i in range(num_units) ]
	#print xij
	return 1

def mutation(rate):
	global node_groups
	ulist=find_edge_units()
	counter=0
	for uid in ulist:#(int(num_units*rate+0.5)):
		if counter>=rate*num_units: break
##        rid=node_groups[uid]
##        ulist2=[x for x in range(num_units) if node_groups[x]==rid and x!=uid]
##        if check_ulist_continuality(ulist2)==0: continue
		r=neighbor_regions(uid)
		if len(r)>=1 and node_groups[uid]!=r[0]:
			node_groups[uid]=r[0]
			counter+=1
	update_district_info()
	if spatial_contiguity==1: repair_fragmented_solution()
	#    else: repair_partial_solution()            
# crossover
#1 overlay sol A and sol B,
#2 select the same facilities in A and B, select other facilities with largest overlays
#3 delete fragemented units
#4 repair by reassigning
	
#mthd
#0 overlay A and B, delete fragements, repair by reassigning
#1\2\3 cover 70% of A on B,  delete fragements, repair by reassigning
#4 inject 30% of A into B
def cross_pdp(sol1,sol2,cmthd,crate):
	global node_groups
	global centersID
	popa=total_pop*1.0/max_num_facility
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_units)]
	sol12=[sol1[x]*10000+sol2[x] for x in range(num_units)]
	rlist=set(sol12)
	rstat={}
	for x in rlist: rstat[x]=0
	for i in range(num_units):
		rstat[sol12[i]]+=nodes[i][3]
	r=[[key,rstat[key]] for key in rstat] #olverlayID, pop
	r.sort(key=lambda x:-x[1])  #dic to list
	pops={}
	if location_problem==2: #pdp, search new centers
		for i in range(max_num_facility):
			ulist=[x for x in range(num_units) if sol12[x]==r[i][0]]
			dmin=MAXNUMBER
			nid=-1
			for k in ulist:
				d=sum(nodedik[x][k] for x in ulist)
				if d<dmin:
					dmin=d
					nid=k
			for x in ulist: node_groups[x]=nid
			centersID[nid]=nid
			pops[nid]=r[i][1]
	#assign large unit at first
	ulist=[ [x,nodes[x][3]] for x in range(num_units) if node_groups[x]==-1]
	ulist.sort(key=lambda x: -x[1])
	ulist=[x[0] for x in ulist]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			if pops[k] + nodes[i][3] <= popa:
				pops[k]+=nodes[i][3]
				node_groups[i]=k
				break
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	for i in ulist:
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			break
	update_district_info()
	repair_fragmented_solution()
	return  
	
	
def cross_flp(sol1,sol2,cmthd,crate):
	global node_groups
	global centersID
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_units)]
	sol12=[sol1[x]*10000+sol2[x] for x in range(num_units)]
	rstat={}
	for x in set(sol12): rstat[x]=0
	for i in range(num_units):
		rstat[sol12[i]]+=nodes[i][3]
	rlist=[[key,rstat[key]] for key in rstat] #olverlayID, pop
	rlist.sort(key=lambda x:-x[1])  #dic to list
	expect_numf=max_num_facility
	if adaptive_number_of_facilities==1:
		expect_numf=random.randint(-1,1)
	print len(rlist),
	for i in range(len(rlist)):
		ulist=[x for x in range(num_units) if sol12[x]==rlist[i][0]]
		if len(ulist)==0:
			print "debug crossover: null area"
		k1=rlist[i][0]/10000
		k2=rlist[i][0]%10000
		k=k1
		if facilityCandidate[k1] in ulist and facilityCandidate[k2] in ulist:
			if random.random()>crate: k=k2
			for x in ulist: node_groups[x]=k
		if facilityCandidate[k1] in ulist and facilityCandidate[k2] not in ulist: 
			for x in ulist: node_groups[x]=k1
		if facilityCandidate[k1] not in ulist and facilityCandidate[k2] in ulist: 
			for x in ulist: node_groups[x]=k2
		if len(set(node_groups))==expect_numf+1: #-1 usually exist
			break
	for k in set(node_groups):
		if k<0: continue
		centersID[k]=facilityCandidate[k]
		u=centersID[k]
		r=node_groups[u]
		if r!=k: print "debug cross:", k,u,r
	#assign fragmented units
	ulist=[x for x in range(num_units) if node_groups[x]==-1]
	for i in ulist:
		k1=sol12[i]/10000
		k2=sol12[i]%10000
		if centersID[k1]>=0 and centersID[k2]>=0: 
			node_groups[i]=k1
			if random.random()>crate: node_groups[i]=k2
			continue
		if centersID[k2]>=0: 
			node_groups[i]=k2
			continue
		if centersID[k1]>=0: 
			node_groups[i]=k1
			continue
		if centersID[k2]>=0: 
			node_groups[i]=k2
			continue
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			break
	update_district_info()
	if spatial_contiguity==1: repair_fragmented_solution()
	if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
		print "Crossover infeasible final solution: continuality "
	return  
	
def cross_sap_simple(sol1,sol2,cmthd,crate):
	global node_groups
	node_groups=sol1[:]
	for i in range(num_units):
		if random.random()>crate:
			node_groups[i]=sol2[i]
	update_district_info()
	if spatial_contiguity==1: repair_fragmented_solution()
	return  
def cross_sap(sol1,sol2,mthdod,rate):
	global node_groups
	node_groups=sol1[:]
	mthd=mthdod
	if mthd==-1:
		mthd=random.randint(0,2)
	#rate=0.1+(crate-0.1)*random.random()
	ulist=[x for x in range(num_units) if sol1[x]!=sol2[x]]

	#uniform random 
	if mthd==0: #insert each unit from sol2 to sol1 with possibility of rate
		for x in ulist:
			if random.random()>rate:
				node_groups[x]=sol2[x]
	#disturb some district
	if mthd==1: #insert each districts from sol2 to sol1 with possibility of rate
		rlist=range(num_districts)
		random.shuffle(rlist)
		rlist=rlist[0:int(num_districts*(1-rate))]
		for x in ulist:
			if node_groups[x] in rlist:
				node_groups[x]=sol2[x]
	#disturb around some district
	if mthd==99:#insert districts 
		rlist=range(num_districts)
		random.shuffle(rlist)
		rlist=rlist[0:int(num_districts*(1-rate))]
		for i in range(num_units):
			if sol2[i] in rlist:
				###noprint ",",
				node_groups[i]=sol2[i]
	#meage splits
	if mthd==2:# districts
		sol12=[sol1[x]*1000+sol2[x] for x in range(num_units)]
		rlist=set(sol12)
		for r in rlist:
			ulist=[x for x in range(num_units) if sol12[x]==r]
			if random.random()>rate:
				k=r%1000
				for u in ulist: node_groups[u]=k
	if spatial_contiguity==1: repair_fragmented_solution()
	##noprint mthd,
	return 
	
def pop_selection(population):
	population1=copy.deepcopy(population)
	population1.sort(key=lambda x:x[0])
	population2=[] #delete identical solution
	#sol=[best_biobjective_global,best_centersID_global[:],best_solution_global[:],best_objective_global,best_objective_fcost_global,best_overload_global,0]
	#population2.append(copy.deepcopy(sol))
	population2.append(copy.deepcopy(population1[0]))
	sdiff=2
	'''if location_problem==3:
		sdiff=max_num_facility/20
		if sdiff<3: sdiff=3
	if max_num_facility>30:
		sdiff=4'''
	for x in population1:
		issimilar=0
		for y in population2:
			rlist=[i for i in range(num_districts) if x[1][i] != y[1][i]]
			if len(rlist)>=sdiff: continue
			else:
				if location_problem>=1:
					issimilar=1
					break
			ulist=[i for i in range(num_units) if x[2][i] != y[2][i]]
			#diffpop=sum(nodes[i][3] for i in ulist)
			#if len(ulist)<min(num_units*1.0/num_districts,num_units/30.0) and diffpop*100.0/total_pop < min(3.0,100.0/num_districts): #100.0/num_districts: #<5%
			#print len(ulist),
			if len(ulist)<num_units*(solution_similarity_limit/100.0):
				issimilar=1
				break
		if issimilar==0:
			population2.append(copy.deepcopy(x))
		#if len(population2)>=min(multi_start_count*3,10):
		#    break
	return population2


def initial_location_solution(idx):
	global node_groups
	global centersID
	global max_exclusion_list
	global max_inclusion_list
	max_exclusion_list=[0.0 for x in range(num_districts)]
	max_inclusion_list=[0.0 for x in range(num_districts)]
	centersID=facilityCandidate[:]
	mthd=initial_solution_method
	if mip_solver not in mip_solvers: mthd=9
	sta=1
	if mthd not in [0,1,8,9]: mthd=9
	if mthd==0:
		location_construction_random()
		#location_construction_drop()
		#if location_problem==1 and len(facilityCandidate)<num_units: location_construction_random()
		#if location_problem==1 and len(facilityCandidate)==num_units: 
		#    centers=k_means()
		#    centersID=[-1 for x in range(num_districts)]
		#    for x in centers: centersID[x]=x
		#    update_district_info()
		#    print biobjective,objective,centers
		#if location_problem==2: location_construction_random()
	if mthd==1:
		sta=CFLP_CKFLP_model(max_num_facility,1,heuristic_time_limit,0.005)
	if mthd==2:
		sta=SSCFLP_SSCKFLP_model(max_num_facility,1,heuristic_time_limit,0.005)
	#if mthd==3: sta=k_medoids()
		#sta=k_means()
	if mthd==8: location_construction_LP() #not used
	if mthd==9:
		sta=LR_main(1000)
		#contiguity
		return 1
	if sta<1:
		location_construction_drop()
	if spatial_contiguity>=1:
		repair_fragmented_solution()        
	return 1
def delete_empty_facility():
	global centersID
	for k in range(num_districts):
		if k not in node_groups:
			centersID[k]=-1

def location_construction_LP():
	lplocs,sol=location_model_linear_relexation(max_num_facility,0,10000,0.01)
	relax_location=[[x,lplocs[x]] for x in range(num_districts)]
	relax_location.sort(key=lambda x:-x[1])
	#print 'relax_location',lplocs
	global node_groups
	global centersID
	centersID=[-1 for x in range(num_districts) ]
	total_supply=0
	for x in relax_location: 
		k=x[0]
		centersID[k]=facilityCandidate[k]
		total_supply+=facilityCapacity[k]
		if total_supply>=total_pop: break
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	RRT_local_search()

def location_construction_random():
	global node_groups
	global centersID
	centersID=[-1 for x in facilityCandidate]
	supply=0
	while 1:
		idx=random.randint(0,num_districts-1)
		if centersID[idx]>=0: continue
		centersID[idx]=facilityCandidate[idx]
		supply+=facilityCapacity[idx]
		nf=sum(1 for x in centersID if x>=0)
		if nf==max_num_facility and adaptive_number_of_facilities==0: break
		if supply>=total_pop and adaptive_number_of_facilities==1: break
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	for i in range(2):
		if location_problem==2: 
			if all_units_as_candadate_locations==1: update_centers()
	VND_local_search()
	return 1
def location_construction_drop(): #drop the facility that cost can be reduced
	global node_groups
	global centersID
	centersID=facilityCandidate[:]
			
	#assign to nearest facility
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]<0: continue
			node_groups[i]=k
			break
	delete_empty_facility()
	update_district_info()
	sta=1
	while sta==1:
		sta=r_r_location_drop_greedy()
		RRT_local_search()
def r_greedy():
	global node_groups
	global centersID
	centersID=[-1 for x in range(num_districts)]
	k=random.randint(0,num_districts)
	centersID[k]=facilityCandidate[k]
	for i in range(num_units): node_groups[i]=k
	while 1:
		#print [x for x in range(num_districts) if centersID[x]>=0],node_groups[:100]
		centers=[x for x in range(num_districts) if centersID[x]>=0]
		if len(centers)==max_num_facility: break
		bestk=-1
		bestobj=0.0
		for k in range(num_districts):
			if centersID[k]>=0: continue
			obj=0.0
			for i in range(num_units):
				k2=node_groups[i]
				if nodedik[i][k]<nodedik[i][k2]: obj+=nodedik[i][k2]-nodedik[i][k]
			if obj>bestobj:
				bestobj=obj
				bestk=k
		centersID[bestk]=bestk
		for i in range(num_units):
			k=node_groups[i]
			if nodedik[i][bestk]<nodedik[i][k]:node_groups[i]=bestk
	update_district_info()
	update_centers()

def generate_initial_solution():
	global best_biobjective_global
	global node_groups
	global centersID
	global all_solutions
	solutions=[]
	t_begin=time.time()
	if initial_solution_method==9:
		initial_solution(0)
		best_biobjective_global=MAXNUMBER  #
		for x in all_solutions: solutions.append(copy.deepcopy(x))#solutions=all_solutions
		if spatial_contiguity>=1:
			best_biobjective_global=MAXNUMBER
			for i in range(len(solutions)):
				location_check(0)
				node_groups=solutions[i][2][:]
				centersID=solutions[i][1][:]
				update_district_info()
				repair_fragmented_solution()
				VND_local_search()
				location_check(1)
				update_best_solution()
				update_region_pool_all()
				solutions[i][2]=node_groups[:]
				solutions[i][1]=centersID[:]
				solutions[i][0]=biobjective
				arcpy_print("init sol "+str(i)+" " +str(solutions[i][0]))
	if initial_solution_method!=9:
		for multi_start in range(multi_start_count):
			sta=initial_solution(multi_start)
		
			location_check(0)
			update_best_solution()
			if spatial_contiguity>=1 and check_solution_continuality_feasibility(node_groups)<1:
				arcpy_print( "0 check_solution_continuality_feasibility(node_groups)...")
			VND_local_search()
			location_check(1)
			if spatial_contiguity>=1 and check_solution_continuality_feasibility(node_groups)<1:
				arcpy_print( "1 check_solution_continuality_feasibility(node_groups)...")
			update_district_info()
			update_best_solution()
			update_region_pool_all()
			solutions.append([biobjective,centersID[:],node_groups[:],objective_overload,0])
			fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
			#print best_biobjective_global,
			nf=sum(1 for x in centersID if x>=0)
			s="initial solution "+str(multi_start+1)+": "+str(nf)+" "+str(fcost)+" "+str(biobjective)+" "+str(objective)+" "+str(objective_overload)
			print s,"conn=",check_current_solution_continuality_feasibility()

	arcpy_print("time for init. solutions: " + str(time.time()-t_begin))
	solutions.sort(key=lambda x:x[0])
	all_solutions=solutions
	return solutions
def initial_solution(idx):
	global node_groups
	global centersID
	global max_exclusion_list
	max_exclusion_list=[0.0 for x in range(num_districts)]
	#for FLP, PDP
	#print "init",idx,location_problem, initial_solution_method
	if location_problem==1: #FLP
		sta=initial_location_solution(idx) #idx
		if spatial_contiguity==1: repair_fragmented_solution()
		return sta
	if location_problem==2: #PDP
		method=initial_solution_method
		if method not in [0,9]: method=0
		if method==0: 
			kmobj,centers,sol=multi_w_k_medoids(1,100,0)
			centersID=[-1 for x in range(num_units)]
			for x in centers: centersID[x]=facilityCandidate[x]
			for x in range(num_units):
				node_groups[x]=centers[sol[x]]
		if method==9: 
			CPMP_LR_main(500) #debug
		#if method==1:
		#    sta=CFLP_CKFLP_model(max_num_facility,1,heuristic_time_limit,0.005)
		update_district_info()
		if spatial_contiguity==1: 
			repair_fragmented_solution()
		return 1
	if location_problem==3: #pmp(m=n)
		sta=-1
		method=initial_solution_method
		if method==0: sta=k_medoids()
		if method==1: sta=r_greedy()
		if method==3: sta=random_centers()
		#if method==8: sta=pmp_sampling()
		#if initial_solution_method==9:  sta=LR_main(1000) #error
		if sta==-1: arcpy_print("no initial solution!!!")
		if spatial_contiguity>=1: repair_fragmented_solution()
		#contiguity
		return 1
	if location_problem==0: #sap,gap
		method=initial_solution_method
		sta=1
		if method not in [0,1,8,9]: method=0
		node_groups=[-1 for x in range(num_units)]
		if method ==0:
			for k in range(num_districts):
				node_groups[nearCustomer[k]]=k
			region_growth()
		if method ==1: sta=TP_model(1)
		if method ==8: assign_diff()
		if method ==9:
			AP_LR_main(500,0.0001,0.001)
		VND_local_search()            
		if spatial_contiguity==1: 
			repair_fragmented_solution()
		return 1

def assign_diff():
	global node_groups
	caplist=[facilityCapacity[x] for x in range(num_districts)]
	ulist=[x for x in range(num_units)]
	while len(ulist)>0:
		udiff=[]
		for x in ulist:
			k1=NearFacilityList[x][0]
			k2=NearFacilityList[x][1]
			k3=NearFacilityList[x][2]
			udiff.append([x,nodedij[x][k1]*2-nodedij[x][k2]-nodedij[x][k3]])
		udiff.sort(key=lambda x:x[1])
		#loops=min(5,len(udiff)/10+1)
		#for loop in range(loops)
		idx=int(random.random()*min(3,len(udiff)))
		x=udiff[idx][0]
		assigned=0
		for r in NearFacilityList[x]:
			if nodes[x][3]<=caplist[r]:
				caplist[r]-=nodes[x][3]
				assigned=1
				node_groups[x]=r
				break
		if assigned==0: node_groups[x]=NearFacilityList[x][0]
		ulist.remove(x)
	update_district_info()

def region_growth():
	global node_groups
	loops=0
	for k in range(num_districts):
		u=centersID[k]
		node_groups[u]=k
		district_info[k][1]=nodes[u][3]
		district_info[k][2]=0.0
		district_info[k][3]=facilityCapacity[k]
	while 1:
		ulist=[x for x in range(num_units) if node_groups[x]==-1] # units not assigned
		if len(ulist)==0: break
		neighbors = []
		for x in ulist:
			for y in node_neighbors[x]:
				if node_groups[y] <0: continue
				nb=[x,node_groups[y],0.0]
				if nb not in neighbors:
					neighbors.append(nb)
		if len(neighbors)<1: break

		if len(neighbors) ==1:
			nid=neighbors[0][0]
			rid=neighbors[0][1]
			node_groups[nid] = rid
			district_info[rid][1]+=nodes[nid][3]
			continue
		for i in range(len(neighbors)):
			nid=neighbors[i][0]
			rid=neighbors[i][1]
			gap=district_info[k][1]+nodes[nid][3]-facilityCapacity[k]*(1+pop_deviation)
			neighbors[i][2]=gap*penalty_on_demand + nodedik[nid][rid]
		#print neighbors
		neighbors.sort(key=lambda x:x[2])
		idx=random.randint(0,1)
		nid=neighbors[idx][0]
		rid=neighbors[idx][1]
		node_groups[nid] = rid #update the solution        
		district_info[rid][1]+=nodes[nid][3]
		loops+=1
	update_district_info()

def update_EDP_centers():
	global node_groups
	global centersID
	global time_update_centers
	t=time.time()
	sol=[-1 for x in range(num_units)]
	centers=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
		kn,ulist=update_center_pmp(k)
		for x in ulist: sol[x]=kn
		centers.append(kn)
		centersID[k]=-1
	node_groups=sol[:]
	for k in centers:
		centersID[k]=facilityCandidate[k]
	update_district_info()
	#print "updatecenters",biobjective-obj
	time_update_centers+=time.time()-t

def update_centers():
	global node_groups
	global centersID
	global time_update_centers
	if envy_service_objective==1:
		return update_center_pmp_envy()
	if location_problem==1 or location_problem==0: return
	t=time.time()
	obj=biobjective
	sol=[-1 for x in range(num_units)]
	centers=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
		kn,ulist=update_center(k)
		if kn==-1:
			print "update center error:",[k,sum(1 for x in range(num_units) if node_groups[x]==k)]," ->", [kn,len(ulist)]
			print NearFacilityList[k][:10],ulist
			kn=k
		if location_problem==3 and centersID[kn]>=0 and k!=kn:
			print "update center error: new center is already used:",k,kn
			kn=k
		if len(ulist)==0:
			print "update center error: ulist is empty:",k,kn,ulist
			kn=k
		for x in ulist: sol[x]=kn
		centers.append(kn)
		centersID[k]=-1
	node_groups=sol[:]
	for k in centers:
		centersID[k]=facilityCandidate[k]
	if location_problem==3 and spatial_contiguity==0:
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break
	obj=biobjective
	update_district_info()
	update_best_solution()
	#print "updatecenters",biobjective-obj
	time_update_centers+=time.time()-t

	#print obj,obj-biobjective
def update_center_pmp_envy():
	global node_groups
	global centersID
	global time_update_centers
	t=time.time()
	obj=biobjective
	sol=[-1 for x in range(num_units)]
	centers=[]
	for k in range(num_districts):
		if centersID[k]==-1: continue
		kn,ulist=update_center_envy(k)
		if kn!=k:
			for x in ulist: node_groups[x]=kn
			centersID[kn]=facilityCandidate[kn]
			centersID[k]=-1
	time_update_centers+=time.time()-t

def update_center_envy(k):
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	best_cost=sum(nodedik[x][k] for x in ulist)*travel_distance_weight
	for u in ulist:
		d=nodedij[u][k]
		if d>envy_service_distance and envy_service_objective==1:
			best_cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
		if d>envy_service_distance and envy_service_objective==4:
			best_cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)
	best_center=k
	for i in range(num_districts):
		cost=sum(nodedik[x][i] for x in ulist)*travel_distance_weight
		for u in ulist:
			d=nodedij[u][i]
			if d>envy_service_distance and envy_service_objective==1:
				cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if d>envy_service_distance and envy_service_objective==4:
				cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)
		if cost<best_cost:
			best_cost=cost
			best_center=i
	return best_center,ulist

def update_cap_centers():
	global node_groups
	global centersID
	global time_update_centers
	t=time.time()
	obj=biobjective
	sol=[-1 for x in range(num_units)]
	centers=[]
	for k in range(num_districts):
		if centersID[k]==-1: continue
		kn,ulist=update_cap_center(k)
		if kn!=k:
			for x in ulist: node_groups[x]=kn
			centersID[kn]=facilityCandidate[kn]
			centersID[k]=-1
	update_cflpr_district_info()
	time_update_centers+=time.time()-t

def update_cap_center(k):
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	demand=sum(nodes[x][3] for x in ulist)
	best_cost=sum(nodedik[x][k] for x in ulist)*travel_distance_weight
	for u in ulist:
		d=nodedij[u][k]
		if d>envy_service_distance and envy_service_objective==1:
			best_cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
		if d>envy_service_distance and envy_service_objective==4:
			best_cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)
	best_center=k
	for i in range(num_districts):
		if centersID[i]>=0: continue
		if demand>facilityCapacity[i]:
			continue
		cost=sum(nodedik[x][i] for x in ulist)*travel_distance_weight
		for u in ulist:
			d=nodedij[u][i]
			if d>envy_service_distance and envy_service_objective==1:
				cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if d>envy_service_distance and envy_service_objective==4:
				cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)
		if cost<best_cost:
			best_cost=cost
			best_center=i
	return best_center,ulist

def update_center(k):
	if location_problem==3: #pmp
		return update_center_pmp(k)
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	best_cost=sum(nodedik[x][k] for x in ulist)
	best_center=k
	for i in range(num_districts):
		demand=district_info[i][1]
		if facilityCapacity[i]<demand: continue
		cost=sum(nodedik[x][i] for x in ulist)
		if cost<best_cost:
			best_cost=cost
			best_center=i
	return best_center,ulist
def update_center_pmp(k): #need debug for PMP with few cands
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	best_cost=MAXNUMBER
	best_center=-1
	klist=[x for x in range(num_districts) if facilityCandidate[x] in ulist]
	for k in klist:
		cost=sum(nodedik[x][k] for x in ulist)
		if cost<best_cost:
			best_cost=cost
			best_center=k
	return best_center,ulist


#reduce overload only
def one_unit_move_pcp(radius,c_percent): #FA
	global node_groups
	global time_op
	#if objective_overload>=0: return 0
	t=time.time()
	klist=[x for x in range(num_districts) if district_info[x][4]>0]
	ulist=[x for x in range(num_units) if node_groups[x] in klist]
	if ulist==[]:
		ulist=[x for x in range(num_units) if nodedij[x][node_groups[x]]>=radius]
	#if ulist==[]: return 0
	random.shuffle(ulist)
	ulist+=[x for x in range(num_units)]
	covered=0
	for x in range(num_units):
		k=node_groups[x]
		if nodedij[x][k]<=radius: covered+=nodes[x][3]
	max_coverd=total_pop*c_percent/100
	improved=0
	for nid in ulist:
		rid=node_groups[nid]
		demand=nodes[nid][3]
		klist=[x for x in NearFacilityList[nid] if centersID[x]>=0]
		klist=klist[:8]
		for k in klist:
			new_covered=covered
			if nodedij[nid][rid]<=radius: new_covered-=demand
			if nodedij[nid][k]<=radius: new_covered+=demand
			if new_covered<max_coverd and new_covered<covered: continue
			overload1=district_info[k][4]+district_info[rid][4]
			overload2=max(0, district_info[rid][1]-demand-facilityCapacity[rid])
			overload2+=max(0, district_info[k][1]+demand-facilityCapacity[k])
			if overload1 < overload2: continue
			if overload1 == overload2 and nodedij[nid][k]>=nodedij[nid][rid]: continue
			#if overload2==overload1: print nodedij[nid][k]-nodedij[nid][rid],
			node_groups[nid]=k
			update_cflpr_district_info()
			covered=new_covered
			#print int(objective),covered, objective_overload
			improved=1
			break
	update_cflpr_district_info()
	time_op[0]+=time.time()-t
	return improved

def two_unit_move_pcp(radius,c_percent): #FA
	global node_groups
	global time_op
	#if objective_overload>=0: return 0
	t=time.time()
	klist=[x for x in range(num_districts) if district_info[x][4]>0]
	ulist=[x for x in range(num_units) if node_groups[x] in klist]
	random.shuffle(ulist)
	covered=0
	for x in range(num_units):
		k=node_groups[x]
		if nodedij[x][k]<=radius: covered+=nodes[x][3]
	max_coverd=total_pop*c_percent/100
	improved=0
	for nid in ulist:
		rid=node_groups[nid]
		demand=nodes[nid][3]
		klist=[x for x in NearFacilityList[nid] if centersID[x]>=0]
		klist=klist[:12]
		for k in klist:
			new_covered=covered
			if nodedij[nid][rid]<=radius: new_covered-=demand
			if nodedij[nid][k]<=radius: new_covered+=demand
			if new_covered<max_coverd and new_covered<covered: continue
			overload1=district_info[k][4]+district_info[rid][4]
			overload2=max(0, district_info[rid][1]-demand-facilityCapacity[rid])
			overload2+=max(0, district_info[k][1]+demand-facilityCapacity[k])
			if overload1 < overload2: continue
			if overload1 == overload2 and nodedij[nid][k]>=nodedij[nid][rid]: continue
			#if overload2==overload1: print nodedij[nid][k]-nodedij[nid][rid],
			node_groups[nid]=k
			update_cflpr_district_info()
			covered=new_covered
			improved=1
			break
	update_cflpr_district_info()
	time_op[0]+=time.time()-t
	return improved

def location_check(key):
	if -1 in node_groups:
		arcpy_print("debug: "+str(key)+ " unit(s) not assigned! ")
		#return -1
	rlist=list(set(node_groups))
	if -1 in rlist: 
		arcpy_print("debug: "+str(key)+ " demand not assigned"+str(rlist))
		#arcpy_print(str(node_groups))
		rlist.remove(-1)
	if len(rlist)>max_num_facility and adaptive_number_of_facilities==0:
		arcpy_print("debug: "+str(key)+ " too many facilities"+str(rlist))
		#return -1
	for k in range(num_districts):
		if k in rlist and centersID[k]==-1:
			arcpy_print("debug: "+str(key)+ " facilitiy not selected but used")
			#return -1
		if centersID[k]>=0 and k not in rlist:
			arcpy_print("debug: "+str(key)+ " facilitiy selected but not used")
			print k, district_info[k],
			print [x for x in centersID if x>=0]
			#return -1
		uid=centersID[k]
		if spatial_contiguity==1 and uid>-1 and node_groups[uid]!=k:
			arcpy_print("debug: "+str(key)+ " facilitiy unit assigned to other facility "+str(k))
			#print k,uid, node_groups[uid]
	'''clist=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
		u=sum (1 for x in range(num_units) if node_groups[x]==k)
		clist.append(u)
	print clist'''
	#return 1

	
def print_solution():
	arcpy_print("_______________final solution_______________")
	for i in range(num_units):
		s=""
		for x in nodes[i]:
			s+=str(x)+"\t"
		k=node_groups[i]
		kunit=centersID[k]
		s+=str(nodes[kunit][4])+"\t"
		selected=-1
		if i in facilityCandidate:
			selected=0
			if i in centersID:
				selected=1
		s+=str(selected)
		arcpy_print(s)
# multistart wrighted k-medoids
#start_num: number of starts
#loop_num: number of loops 
#connective: constraints on spatial contiguity? 1 for yes and 0 for no 
def multi_w_k_medoids(start_num, loop_num,connective):
	global node_groups
	global avg_pop  
	global avg_dis_min
	avg_pop=total_pop*1.0/max_num_facility
	wk_bestobj=MAXNUMBER
	wk_centers=[]
	wk_sol=[]
	for i in range(start_num):
		centers=k_means()  #change centersxy
		obj,dis,newcenters,sol=weighted_k_medoids(centers,loop_num,connective)
		biobj=obj
		if biobj < wk_bestobj:
			wk_bestobj=biobj
			wk_centers=newcenters[:]
			wk_sol=sol[:]
		avg_dis_min=dis/total_pop
	return wk_bestobj,wk_centers, wk_sol

# return k centers by k-means
def k_means():
	global centersID
	global node_groups
	centers=[]
	centersxy=[[0.0,0.0] for x in range(max_num_facility)]
	sol=[-1 for x in range(num_units)]
	#random centers
	#for i in range(num_units):
	#    if nodes[i][3]>=avg_pop:
	#        centers.append(i)
	while 1:
		nid=random.randint(0,num_units-1)
		if nid not in centers:
			centers.append(nid)
		if len(centers)==max_num_facility:
			break
	for k in range(max_num_facility):
		cid=centers[k]
		centersxy[k][0]=nodes[cid][1]
		centersxy[k][1]=nodes[cid][2]
	loop=0
	distance_obj=MAXNUMBER
	#k-means
	while 1:
		loop+=1
		#print  centersxy
		sol = [-1 for x in range(num_units)]
		#random.shuffle(nodelist)
		total_d=0.0
		#assign node to center
		for i in range(num_units):
			cid=-1
			d=MAXNUMBER
			for k in range(max_num_facility):
				dx=nodes[i][1]-centersxy[k][0]
				dy=nodes[i][2]-centersxy[k][1]
				#dxy=pow(dx*dx+dy*dy,0.5)
				dxy=dx*dx+dy*dy
				if dxy<d:
					d=dxy
					cid=k
			sol[i]=cid
		for k in range(max_num_facility):
			klist=[x for x in range(num_units) if sol[x]==k]
			if len(klist)==0:
				continue
			dx=sum(nodes[x][1]*nodes[x][3] for x in klist)
			dy=sum(nodes[x][2]*nodes[x][3] for x in klist)
			dsum=sum(nodes[x][3] for x in klist)
			centersxy[k][0]=dx/dsum
			centersxy[k][1]=dy/dsum
		obj=0.0
		for i in range(num_units):
			k=sol[i]
			dx=nodes[i][1]-centersxy[k][0]
			dy=nodes[i][2]-centersxy[k][1]
			dxy=pow(dx*dx+dy*dy,0.5) * nodes[i][3]
			obj+=dxy
		if obj<distance_obj:
			distance_obj=obj
		else:
			break
		#print loop, distance_obj,obj
	centers=[]
	for k in range(max_num_facility):
		ulist=[x for x in range(num_units) if sol[x]==k]
		kdis=MAXNUMBER
		kcenter=-1
		for x in range(num_districts):
			tmp=0.0
			for y in ulist:
				#tmp+=nodedij[y][x]*nodes[y][3]*(10+random.random())/10
				tmp+=nodedik[y][x]
			if tmp<kdis:
				kdis=tmp
				kcenter=x
		centers.append(kcenter)
	#print "k-means",distance_obj,centers
	centersID=[-1 for x in range(num_districts)]
	for x in centers: centersID[x]=x
	node_groups=[centers[x] for x in sol]
	update_district_info()
	return centers
def random_centers():
	global centersID
	centers=[]
	while 1:
		if len(centers)==max_num_facility: break
		k=random.randint(0,num_districts-1)
		if k not in centers: centers.append(k)
	for x in range(num_districts):centersID[x]=-1
	for x in centers: centersID[x]=facilityCandidate[x]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	return 1
		

# return k centers by k-means
def k_medoids():
	global centersID
	global node_groups
	centers=[]
	sol=[-1 for x in range(num_units)]
	sol2=[-1 for x in range(num_units)]
   
	#while 1:
	#    nid=random.randint(0,num_units-1)
	#    if nid not in centers:
	#        centers.append(nid)
	#    if len(centers)==max_num_facility:
	#        break
	random_centers()
	centers=[x for x in range(num_districts) if centersID[x] >=0]
	loop=0
	distance_obj=MAXNUMBER
	#k-means
	while 1:
		loop+=1
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if k in centers:
					sol[i]=k
					break
		obj=0.0
		for k in range(max_num_facility):
			ulist=[x for x in range(num_units) if sol[x]==centers[k]]
			if len(ulist)==0: continue
			clist=range(num_districts)
			cid=-1
			mindis=MAXNUMBER
			for i in clist:
				dsum=sum(nodedik[x][i] for x in ulist)
				if dsum<mindis:
					mindis=dsum
					cid=i
			centers[k]=cid
			obj+=mindis
			for i in ulist: sol2[i]=cid
		sol=sol2[:]
		if obj<distance_obj:
			distance_obj=obj
		else:
			break
		#print loop, distance_obj,obj,centers
	#print "k-means",distance_obj,centers
	centersID=[-1 for x in range(num_districts)]
	for x in centers: centersID[x]=facilityCandidate[x]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	#update_centers()
	return 1

def k_medoids_sampling(allulist,cids):
	centers=cids
	num=len(allulist)
	if centers==[]:
		while 1:
			k=random.randint(0,num_districts-1)
			if k not in centers:
				centers.append(k)
			if len(centers)==max_num_facility:
				break
	sol=[-1 for x in allulist]
	loop=0
	distance_obj=MAXNUMBER
	#k-means
	while 1:
		loop+=1
		for idx in range(len(allulist)):
			i=allulist[idx]
			for k in NearFacilityList[i]:
				if k in centers:
					sol[idx]=k
					break
		obj=0.0
		for k in centers:
			ulist=[allulist[x] for x in range(num) if sol[x]==k]
			if len(ulist)==0: continue
			mindis=sum(nodedik[x][k] for x in ulist)
			cid=k
			for i in range(num_districts):
				dsum=sum(nodedik[x][i] for x in ulist)
				if dsum<mindis:
					mindis=dsum
					cid=i
			idx=centers.index(k)
			centers[idx]=cid
			obj+=mindis
		#print loop,distance_obj,sol
		if obj<distance_obj:
			distance_obj=obj
		else:
			break
	centers=list(set(centers))
	return distance_obj,centers


def K_means_uflp(allulist,cids):
	global node_groups
	global centersID
	old_fcost=sum(facilityCost[x] for x in cids)
	old_obj=old_fcost*fixed_cost_obj
	old_obj+=sum(nodedik[x][node_groups[x]] for x in allulist)
	old_capa=sum(facilityCapacity[x] for x in cids)
	
	num=len(allulist)
	centers=[]
	for x in cids:
		u=nearCustomer[x]
		klist=[]        
		for k in NearFacilityList[u]:
			if k in cids: continue
			if k in klist: continue
			klist.append(k)
			if len(klist)>3: 
				random.shuffle(klist)
				centers.append(klist[0])        
				break       
	random.shuffle(centers)
	nf=random.randint(0,3)
	if nf<=1: centers.pop()
	if nf>=3: 
		idx=random.randint(0,num-1)
		for k in NearFacilityList[allulist[idx]]:
			if k in centers: continue
			if centersID[k]>=0: continue
			centers.append(k)
			break
	sol=[node_groups[x] for x in allulist]
	obj=sum(facilityCost[x] for x in centers)
	obj+=sum(nodedik[allulist[i]][sol[i]] for i in range(num))

	while 1:
		for idx in range(num):
			i=allulist[idx]
			for k in NearFacilityList[i]:
				if k in centers:
					sol[idx]=k
					break
		improved=0
		for k in centers:
			ulist=[allulist[x] for x in range(num) if sol[x]==k]
			if len(ulist)==0: continue
			demand=sum(nodes[x][3] for x in ulist)
			mindis=fixed_cost_obj*facilityCost[k]+ sum(nodedik[x][k] for x in ulist)
			#mindis= sum(nodedik[x][k] for x in ulist)
			cid=k
			for i in range(num_districts):
				if facilityCapacity[i]<demand*0.9: continue
				dsum=fixed_cost_obj*facilityCost[i]+sum(nodedik[x][i] for x in ulist)
				#dsum=sum(nodedik[x][i] for x in ulist)
				if dsum<mindis:
					mindis=dsum
					cid=i
			if k!=cid:
				improved=1
				idx=centers.index(k)
				centers[idx]=cid
				for x in ulist:
					idx=allulist.index(x)
					sol[idx]=cid
		if improved==0: break
		#print ".",
	'''centers=list(set(centers))
	for x in cids: centersID[x]=-1
	for x in centers: centersID[x]=x
	for idx in range(num):
		i=allulist[idx]
		node_groups[i]=sol[idx]'''
	fcost2=sum(facilityCost[x] for x in centers)
	obj2=fcost2*fixed_cost_obj    
	obj2+=sum(nodedik[allulist[i]][sol[i]] for i in range(num))
	capa2=sum(facilityCapacity[x] for x in centers)
	sta=0
	if obj2>old_obj:
		return 0, centers,sol        
	if capa2<old_capa and objective_supply+capa2-old_capa<total_pop: 
		return 0, centers,sol        
	if max_facility_cost>0:
		if fcost2>old_fcost and objective_fcost+fcost2-old_fcost>max_facility_cost:
			return 0, centers,sol        
	print [objective_fcost,fcost2, old_fcost,objective_fcost+fcost2-old_fcost]
	return 1,centers,sol
#wrighted k-medoids
#start_num: number of starts
#loop_num: number of loops 
#connective: constraints on spatial contiguity? 1 for yes and 0 for no    
def weighted_k_medoids(centers,loops,connective):
	global node_groups
	global centersID
	weight=[1.0 for x in range(max_num_facility)]
	gaps=[0.0 for x in range(max_num_facility)]
	kw_centers=centers[:]
	sol=[-1 for i in range(num_units)]
	loop=0
	distance_best=MAXNUMBER
	bal_best=MAXNUMBER
	obj_best=MAXNUMBER
	best_centers=[]
	best_sol=[]
	for k in range(max_num_facility):
		weight[k]=1.0
	while loop<loops:
		loop+=1
		sol = [-1 for x in range(num_units)]
		total_d=0.0
		#assign node to center
		for i in range(num_units):
			cid=-1
			d=MAXNUMBER
			for k in range(max_num_facility):
				dxy=nodedij[i][kw_centers[k]]*weight[k]
				if dxy<d:
					d=dxy
					cid=k
			sol[i]=cid
			total_d+=d
		#if connective:
		#    repair_fragmented_solution()        

		for k in range(max_num_facility):
			ulist=[x for x in range(num_units) if sol[x]==k]
			kdis=MAXNUMBER
			kcenter=-1
			for x in range(num_districts):
				if facilityCandidate[x] not in ulist: continue
				tmp=0.0
				for y in ulist:
					tmp+=nodedik[y][x]*(9.5+random.random())/10
				if tmp<kdis:
					kdis=tmp
					kcenter=x
			kw_centers[k]=kcenter
		
		dis=0.0
		for k in range(max_num_facility):
			ulist=[x for x in range(num_units) if sol[x]==k]
			#dis+=sum(nodedij[x][kw_centers[sol[x]]]*nodes[x][3] for x in ulist)
			dis+=sum(nodedik[x][kw_centers[sol[x]]] for x in ulist)
			pop=sum(nodes[x][3] for x in ulist)
			gaps[k]=pop
		gap=0.0
		for pop in gaps:
			if pop<avg_pop*(1-pop_deviation):
				gap+=avg_pop*(1-pop_deviation)-pop
			if pop>avg_pop*(1+pop_deviation):
				gap+=pop-avg_pop*(1+pop_deviation)
		obj=dis + dis/total_pop*gap*penalty_on_demand
		if obj<obj_best:
			obj_best=obj
			bal_best=gap
			best_centers=kw_centers[:]
			best_sol=sol[:]
			distance_best=dis   
	  
		#update weights
		for k in range(max_num_facility):
			weight[k]*=pow(1-loop*1.0/loops,0.5)+pow(loop*1.0/loops,0.5)*(gaps[k])/avg_pop
		avgw=sum(x for x in weight)/max_num_facility
		for k in range(max_num_facility):
			weight[k]/=avgw
		#print "loop",loop, obj_best,distance_best,kw_centers            
	return obj_best,distance_best,best_centers,best_sol
	

def ga(numf,multistarts,timelimit,mthd,crate, mrate,spp,myseed):
	global multi_start_count
	global seed
	global acceptanceRule
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	global move_count
	global region_pool
	global pool_index
	global is_spp_modeling
	global spp_loops
	global all_solutions
	global assignment_operators_selected
	global max_num_facility
	global heuristic_time_limit
	global adjust_mutation_rate
	max_num_facility=numf
	if location_problem==0:
		max_num_facility=num_districts
	initialize_instance()
	cur_crate=crate
	cur_mrate=mrate
	heuristic_time_limit=timelimit
	mutation_rate_adjustmented=int(mrate*num_units) #param
	#evolution_stats=[]
	pop_dis_coeff_fitness=2.0
	acceptanceRule='ga'
	is_spp_modeling=spp
	if mip_solver not in mip_solvers: is_spp_modeling=-1
	all_solutions=[]
	multi_start_count=multistarts
	if multi_start_count<2: 
		multi_start_count=2

	seed=myseed
	if seed<0:
		seed=random.randint(0,100)
	random.seed(seed)
	##noprint "seed",seed
	region_pool=[]
	ga_time=0.0
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]

	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	optimum=99.99
	t_ga=time.time()
	multi_start=0

	population=generate_initial_solution()

	stats_mutation=[]
	not_improved=0
	improved_time=time.time()
	loop=0
	while 1:
		pop_dis_coeff_fitness=1+2*random.random()
		if time.time()-t_ga > heuristic_time_limit:  break
		r=random.random()
		idx1 = int(min(multi_start_count/2,len(population))* pow(r,1))
		r=random.random()
		idx2 = int(min(multi_start_count,len(population)) * pow(r,1))
		if idx1==idx2: continue
		loop+=1
		sol1=population[idx1][2]
		sol2=population[idx2][2]
		#p_obj=population[idx1][0]
		#step2: crossover
		cur_mrate=(1+random.random())*mrate/2
		if random.random()<0.3 or mthd==9:
			node_groups=population[idx1][2][:]
			centersID=population[idx1][1][:]
			update_district_info()
			#location_check(1)     
		else:
			if location_problem==0: cross_sap(sol1,sol2,mthd,cur_crate)
			if location_problem==1: cross_flp(sol1,sol2,mthd,cur_crate)
			if location_problem==2: 
				cross_pdp(sol1,sol2,mthd,cur_crate)
				#update_centers()
			update_best_solution()
			update_region_pool_all()
			#location_check(2)      
		#step2b: local search
		#print biobjective,
		VND_local_search()
		if location_problem==2 or location_problem==3: 
			if all_units_as_candadate_locations==1: update_centers()
		if location_problem==1 and num_districts==len(facilityCandidate): update_centers()
		#location_check(3)     
		obj1=biobjective
		update_region_pool_all()
		fitness=biobjective
		fcost=0.0
		if location_problem==1:
			fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
			fitness=objective+fcost
			fitness+=objective_overload*fitness/total_pop*pop_dis_coeff_fitness
		population.append([biobjective,centersID[:],node_groups[:],objective+fcost,objective_overload,fitness])

		sign ="+"
		if biobjective < min(population[idx1][0],population[idx2][0]): sign="-"
		if biobjective < best_biobjective_global:
			sign="*"
		#print sign,
		#step3: mutation
		#p_obj=biobjective
		cur_mrate=(1+random.random())*mrate/2
		#mutation(cur_mrate)
		assign_ruin_recreate(-1)
		#location_check(5)
		update_best_solution()
		update_region_pool_all()
		#step4b: local search
		#print biobjective,
		VND_local_search()
		obj2=biobjective
		#location_check(6)             #print biobjective,
		update_region_pool_all()
		sign2 ="+"
		if biobjective+0.0000001 < obj1: sign="-"
		if biobjective < best_biobjective_global: sign="*"
		sign+=sign2
		fitness=biobjective
		fcost=0.0
		if location_problem==1:
			fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
			fitness=objective+fcost
			fitness+=objective_overload*fitness/total_pop*pop_dis_coeff_fitness
		population.append([biobjective,centersID[:],node_groups[:],objective+fcost,objective_overload,fitness])
		not_improved+=1
		if min(obj1,obj2)<population[0][0]*0.9999999999: not_improved=0
		#step4 update population
		#for i in range(len(population)): population[i][5]=population[i][3]+population[i][4]*population[i][3]/total_pop*pop_dis_coeff_fitness
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		while len(population)>multi_start_count*2:
			population.pop()

		all_solutions=population
		nf=sum(1 for x in best_centersID_global if x>=0)
		s="GA loop "+str(loop) +" "+sign+" best: " +str(nf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		nf=sum(1 for x in centersID if x>=0)
		s+=" current: " +str(nf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_overload))
		s+= " [" +str(int(population[0][0])) +"-" +str(int(population[-1][0])) +"] " + str(not_improved)
		arcpy_print(s)
		if not_improved>=max_loops_solution_not_improved: break
	population.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #population[0][2][:]
	centersID=best_centersID_global
	update_district_info()
	##noprint "all solutions:"
	#for x in  all_solutions:
	#    ##noprint x[0:-1]
	ga_time=time.time()-t_ga
	print "GA solution:",biobjective,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		sppmodel(heuristic_time_limit,0.0001)
		update_district_info()
		update_best_solution()
		##noprint "number of areas recorded", len(region_pool)
		##noprint "spp solution:",biobjective,objective,objective_overload,time.time()-t_spp, time.time()-t
		s="SPP solution: "+ str(biobjective)+" "+str(objective) + " " +str(objective_overload)+ " " +str(time.time()-t_spp)
		arcpy_print(s)
	t_vnd=time.time()
	#if 1 not in assignment_operators_selected: assignment_operators_selected.append(1)
	#elif 2 not in assignment_operators_selected: assignment_operators_selected.append(2)
	#VND_local_search()
	##noprint "final LS solution:",biobjective,objective,objective_overload
	#s="VND solution: "+ str(biobjective)+" "+str(objective) + " " +str(objective_overload)+ " " +str(time.time()-t_vnd)
	#arcpy_print(s)
	population.append([biobjective,centersID[:],node_groups[:],objective+fcost,objective_overload,0])
	all_solutions=population
	population.sort(key=lambda x:x[0])
	sta=check_solution_continuality_feasibility(node_groups)
	arcpy_print("solution continuality(1 yes,0 no): "+str(sta))
	search_stat()
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

def assign_ruin_recreate(idx):
	global time_ruin_recreate
	#if location_problem==4: return -1,1
	t=time.time()
	if idx<0 and len(ruin_oprators)<1: return -1
	ruin_idx=idx
	if idx<0:
		r=random.randint(0,len(ruin_oprators)-1)
		ruin_idx=ruin_oprators[r]
	#ruin_idx=0~4, diversification
	if ruin_idx==0: r_r_perb_location()
	if ruin_idx==1: r_r_perb_district()
	if ruin_idx==2: r_r_large_region()
	if ruin_idx==3: r_r_perb_edge_units()
	if ruin_idx==4: r_r_perb_mutation()

	if ruin_idx==9: #move a few locations for PMP, PDP
		r_r_perb_center_locations()
	if spatial_contiguity>=1: 
		repair_fragmented_solution()
	time_ruin_recreate[ruin_idx]+=time.time()-t
	return ruin_idx,1
def assign_ruin_recreate_pmp_envy(strength): #for pmp only, debuging
	if random.random()>0.5:
		assign_ruin_recreate_pmp_envy1(strength)
	else:
		assign_ruin_recreate_pmp_envy2(strength)

def assign_ruin_recreate_pmp_envy1(strength): #for pmp only, debuging
	global node_groups
	global centersID
	u=random.randint(0,num_units-1)
	klist=[x for x in NearFacilityList[u] if centersID[x]>=0]
	klist=klist[:strength]
	for k in klist:
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		random.shuffle(ulist)
		for nk in NearFacilityList[ulist[0]]:
			if centersID[nk] >=0: continue
			if nk in klist: continue
			if centersID[nk]<0:
				centersID[k]=-1
				centersID[nk]=facilityCandidate[nk]
				break
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	if spatial_contiguity==1:
		repair_fragmented_solution()
def assign_ruin_recreate_pmp_envy2(strength): #for pmp only, debuging
	global node_groups
	global centersID
	klist=[x for x in range(num_districts) if centersID[x]>=0]
	random.shuffle(klist)
	klist=klist[:strength]
	for k in klist:
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		random.shuffle(ulist)
		for nk in NearFacilityList[ulist[0]]:
			if centersID[nk] >=0: continue
			if nk in klist: continue
			if centersID[nk]<0:
				centersID[k]=-1
				centersID[nk]=facilityCandidate[nk]
				break
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	if spatial_contiguity==1:
		repair_fragmented_solution()

def r_r_perb_center_locations(): #for pmp only, debuging
	global node_groups
	global centersID
	old_centersID=centersID[:]
	while 1:
		u=random.randint(0,num_units-1)
		k=node_groups[u]
		if centersID[k]==-1: continue
		for nk in NearFacilityList[u]:
			if nk==k: continue
			if centersID[nk]<0:
				centersID[k]=-1
				centersID[nk]=facilityCandidate[nk]
				break
		diff=sum(1 for x in range (num_districts) if centersID[x]!=old_centersID[x])
		if diff>=3: break
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]>=0:
				node_groups[i]=k
				break
	update_district_info()
	if spatial_contiguity==1:
		repair_fragmented_solution()


def MIP_location_search():
	global centersID
	old_ids=centersID[:]
	rlist=select_region(-1)
	ulist=[x for x in range(num_units) if node_groups[x] in rlist]
	sol=location_sub_model(rlist,ulist,0.0001)
	if len(sol)==0: return 0
	nlist=list(set(sol))
	nlist.sort()
	if -1 in nlist: nlist.remove(-1)
	for i in range(num_units):
		if sol[i]<0: continue
		node_groups[i]=sol[i]
	centers=set(node_groups)
	centersID=[-1 for x in range(num_districts)]
	for x in centers: centersID[x]=facilityCandidate[x]
	update_district_info()
	#if all_units_as_candadate_locations==1 or num_units==len(facilityCandidate): one_unit_move()
	return 1

def MIP_UFLP_location_search():
	global centersID
	global node_groups
	old_ids=centersID[:]
	uid=random.randint(0,num_units-1)
	rlist=NearFacilityList[uid]
	rlist=[x for x in rlist if centersID[x]>=0]
	nf=sum(1 for x in centersID if x>=0)
	n=min(10,(nf+1)/2)
	rlist=rlist[:n]
	uflp_sub_model(rlist,0.0000000002)
	for i in range(num_units-1):
		k=node_groups[i]
		for j in NearFacilityList[i]:
			if centersID[j]<0: continue
			if j!=k: 
				node_groups[i]=j
				#print "j!=k", i,nodedij[i][k],nodedij[i][j]
			break
	return 1
def check_pmp_sol(pos):
	for i in range(num_units):
		k=node_groups[i]
		if centersID[k]<0: print i,k,"centersID[k]<=0",pos
		for j in NearFacilityList[i]:
			if centersID[j]<0: continue
			if k!=j and nodedik[i][k]!=nodedik[i][j] and spatial_contiguity==0: 
				print i,k,nodedik[i][k],j,nodedik[i][j],"k is not the nearest facility",pos
			break
	print pos,"best=",best_biobjective_global,"obj=",biobjective,"conn=",check_solution_continuality_feasibility(node_groups),
	print check_current_solution_continuality_feasibility()

def ils_pmp(numf,multistarts,timelimit,myseed):
	global multi_start_count
	global seed
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	#global node_neighbors
	global move_count
	global region_pool
	global pool_index
	global is_spp_modeling
	global spp_loops
	global all_solutions
	global assignment_operators_selected
	global max_num_facility
	global heuristic_time_limit
	global adjust_mutation_rate
	global large_facility_cost
	global initial_solution_method
	global avg_dis_min
	global spatial_contiguity
	global location_tabu_list
	global max_exclusion_list
	max_num_facility=numf
	if location_problem==0:
		max_num_facility=num_districts
	initialize_instance()
	heuristic_time_limit=timelimit
	all_solutions=[]
	multi_start_count=multistarts
	seed=myseed
	if seed<0:
		seed=random.randint(0,100)
	random.seed(seed)
	arcpy_print("seed: "+str(seed))
	region_pool=[]
	t=time.time()
	ga_time=0.0
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[]
	if is_spp_modeling>=1:
		pool_index=[[] for x in range(num_districts)]
	t_ga=time.time()
	multi_start=0

	population=generate_initial_solution()
	if len(max_exclusion_list)<1:
		max_exclusion_list=[0.0 for x in range(num_districts)]
	not_improved_global=0
	improved_time=time.time()
	loop=-1
	while 1:
		loop+=1
		r=random.random()
		sidx = int(min(multi_start_count,len(population))* pow(r,2)*0.999)
		r=random.random()
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_district_info()
		current=" current: " +str(int(population[sidx][0]))+" -> "
		not_improved_global+=1
		old_ids=centersID[:]
		best_obj=best_biobjective_global
		cur_obj=biobjective
		op=0
		sta=0
		#check_pmp_sol(0)
		if random.random()>0.5:
			idx,sta=r_r_new_location(-1)
		else:
			assign_ruin_recreate(-1)
			op=1
		if spatial_contiguity>=1: VND_local_search()
		#update_centers()
		#if spatial_contiguity>=1: repair_fragmented_solution()
		#    check_pmp_sol(4)
		#check_pmp_sol(1)
		update_district_info()
		update_best_solution()
		update_region_pool_all()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,max(0,total_pop-objective_supply)])
		s=""
		if biobjective<best_obj:  #0.1%
			s="*"
			impp=((biobjective-best_obj)/biobjective)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		elif biobjective<cur_obj-0.000001: 
			s="#"
		else: s="-"
		s=str(op)+" "+s
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Search loop "+str(loop) + " best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		nf=sum(1 for x in centersID if x>=0)
		s+=current + str(nf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_overload))
		f=[x for x in range(num_districts) if max_exclusion_list[x] <=best_biobjective_global+0.00001]
		n=sum(1 for x in range(num_districts) if best_centersID_global[x]>=0 and x in f) 
		s+=" "+ str(n)
		surplus=int(objective_supply-total_pop)
		psize=int(total_pop/nf)
		s+= " Info: " +str(len(population))+" " +str(len(potential_facilities)) +" " + str(surplus)+"/"+str(psize)+" " +str(not_improved_global)+ " "+str(int(time.time()-t_ga))
		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		#while len(population)>multi_start_count*5:
		#    population.pop()
		all_solutions=population
		if time.time()-t_ga > heuristic_time_limit:  break
	#post procedure

	population.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #population[0][2][:]
	centersID=best_centersID_global[:]
	update_district_info()
	ga_time=time.time()-t_ga
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sppmodel(heuristic_time_limit,0.000001)
		update_district_info()
		update_centers()
		update_best_solution()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		print "spp solution:",biobjective,objective_fcost,objective,objective_overload,time.time()-t_spp, time.time()-t_spp
	print "final solution:",biobjective,objective_fcost,objective,objective_overload
	population.sort(key=lambda x:x[0])
	all_solutions=population
	sta=check_solution_continuality_feasibility(node_groups)
	print "Areal continuality(1 yes, 0 no):",sta
	if spatial_contiguity==1:
		if sta==0:    return "infeasible final solution: continuality"
	##noprint "time",time.time()-t
	search_stat()
	print "location_tabu_list",len(location_tabu_list)
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

#solve pmp, melp, mdelp, uflp, ce-uflp
def ils_pmp_fast(numf,swapMethod):
	global best_biobjective_global
	global biobjective
	global node_groups
	global centersID
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	global max_num_facility
	max_num_facility=numf
	initialize_instance()
	all_solutions=[]
	region_pool=[]
	t=time.time()
	ga_time=0.0
	best_biobjective_global = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[]
	Facility2List=[-1 for x in range(num_units)]
	gainList=[0.0 for x in range(num_districts)] #gian(fi)
	lossList=[0.0 for x in range(num_districts)] #loss(fr)
	extraList=[[0.0 for x in range(num_districts)] for y in range(num_districts)] #extra( fi, fr)
	if is_spp_modeling>=1:
		pool_index=[[] for x in range(num_districts)]
	t_ga=time.time()
	for idx in range(multi_start_count):
		best_biobjective = MAXNUMBER
		n=max_num_facility
		if adaptive_number_of_facilities==1 and max_facility_cost==0:
			n=max(5,num_districts/15)
			if max_facility_cost>0:
				n=int(max_facility_cost*num_districts/sum(facilityCost))
			add=[-2,-1,-1,0,0,0,1,1,2]                
			random.shuffle(add) 
			n+=add[0]
		if max_facility_cost>0:
			n= int(max_facility_cost*num_districts/sum(facilityCost)+0.5)
		clist=range(num_districts)
		random.shuffle(clist)
		clist=clist[:n]
		centersID=[-1 for x in range(num_districts)]
		for x in clist: centersID[x]=x
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break            
		update_envy_district_info()
		nf2=sum(1 for x in centersID if x>=0)
		update_envy_district_info()
		sta=1
		swap=swapMethod
		if swap==3:
			swap=random.randint(1,2)
		if swap==2:
			Renato_update(Facility2List,gainList,lossList,extraList)
		while sta>0:
			#print ".",
			if swap==-1:
				sta=pmp_TB()
			if swap==1:
				sta=pmp_Whitaker()#tested        
			if swap==2:
				sta=pmp_Renato(Facility2List,gainList,lossList,extraList)#bug
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_best_solution()
		rr_obj=biobjective
		update_best_solution()
		update_region_pool_all()            
		all_solutions.append([biobjective,centersID[:],node_groups[:]])
		nf=sum(1 for x in centersID if x>=0)
		print "init solution", idx, nf2,nf,biobjective,objective,time.time()-t_ga
	not_improved_global=0
	population=all_solutions
	population.sort(key=lambda x:x[0])
	if numf==1: return []

	improved_time=time.time()
	loop=-1
	while 1:
		if not_improved_global >= max_loops_solution_not_improved: break
		loop+=1
		r=random.random()
		sidx = int(min(multi_start_count,len(population))* pow(r,1.5)*0.999)
		r=random.random()
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_envy_district_info()
		current=" current: " +str(int(population[sidx][0]))+" -> "
		not_improved_global+=1
		old_ids=centersID[:]
		best_obj=best_biobjective_global
		cur_obj=biobjective
		strength=3
		while 1:
			nf=sum(1 for x in centersID if x>=0)
			if nf<4: break            
			strategy=[[2,1],[2,3],[2,2],[3,2],[3,3],[3,4],[4,3],[4,4],[4,5]]
			if adaptive_number_of_facilities==0:
				maxStrength=max(4, int(nf*ruin_percentage+50)/100)
				maxStrength=min(8,maxStrength)
				strength=random.randint(3,maxStrength)
				strategy=[[strength,strength]]
			'''if adaptive_number_of_facilities==1:
				maxStrength=max(4, int(nf*ruin_percentage+50)/100)
				maxStrength=min(8,maxStrength)
				strength=random.randint(3,maxStrength)
				e=random.randint(-1,1)
				strategy=[[strength,strength+e]]'''
			idx=random.randint(0,len(strategy)-1)
			strength=sum(strategy[idx])
			clist=[x for x in range(num_districts) if centersID[x]<0]
			if len(clist)<=strategy[idx][0]: continue
			random.shuffle(clist)
			for x in range(strategy[idx][0]):
				k=clist[x]
				centersID[k]=facilityCandidate[k]
			clist=[x for x in range(num_districts) if centersID[x]>=0]
			if len(clist)<=strategy[idx][1]: continue
			random.shuffle(clist)
			for x in range(strategy[idx][1]):
				k=clist[x]
				centersID[k]=-1
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]>=0:
						node_groups[i]=k
						break
			update_envy_district_info()
			break
		fcost =sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		#reset_search_inro
		swap=swapMethod
		if swapMethod==3:
			swap=random.randint(1,2)
		if swap==2:Renato_update(Facility2List,gainList,lossList,extraList)
		rr_obj=biobjective
		while 1:
			sta=-1
			if swap==-1:
				sta=pmp_TB()
			if swap==1:
				sta=pmp_Whitaker()#tested
			if swap==2:
				sta=pmp_Renato(Facility2List,gainList,lossList,extraList)#bug
			if sta!=1:
				break
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_envy_district_info()
		update_best_solution()
		update_region_pool_all()
	
		s=""
		if biobjective<best_obj:  #0.1%
			#del population[sidx]
			s="*"
			impp=((biobjective-best_obj)/biobjective)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
			#population.append([biobjective,centersID[:],node_groups[:]])
		elif biobjective<cur_obj: 
			#del population[sidx]
			s="#"
			#population.append([biobjective,centersID[:],node_groups[:]])
		else: 
			s="-" 
			#del population[sidx]
		population.append([biobjective,centersID[:],node_groups[:]])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		if len(population)>max(10, multi_start_count*2):
			population.pop()
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Search loop "+str(loop) + " best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))
		nf=sum(1 for x in centersID if x>=0)
		s+=current + str(nf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_fcost))
		s+= " Info: " +str(len(population))+" " +str(not_improved_global)+ " "+str(int(time.time()-t_ga))
		s+= " Imp: "+ str(strength)+":"+str(int(biobjective-cur_obj))
		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		#while len(population)>multi_start_count*5:
		#    population.pop()
		all_solutions=population
		if time.time()-t_ga > heuristic_time_limit:  break
		if stop_searching==1: break
		#print check_current_solution_continuality_feasibility()
	#post procedure
	population.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #population[0][2][:]
	centersID=best_centersID_global[:]
	update_envy_district_info()
	ga_time=time.time()-t_ga
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sppmodel((time.time()-t_ga)/10,0.000001)
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break
		update_envy_district_info()
		#update_centers()
		update_best_solution()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		print "spp solution:",biobjective,objective_fcost,objective,objective_overload,time.time()-t_spp, time.time()-t_spp
		update_best_solution()
		node_groups=best_solution_global[:] #population[0][2][:]
		centersID=best_centersID_global[:]
		update_envy_district_info()

	print "final solution:",biobjective,objective_fcost,objective,objective_overload
	population.sort(key=lambda x:x[0])
	all_solutions=population
	#sta=check_solution_continuality_feasibility(node_groups)
	#print "Areal continuality(1 yes, 0 no):",sta
	#if spatial_contiguity==1:
	#    if sta==0:    return "infeasible final solution: continuality"
	##noprint "time",time.time()-t
	#search_stat()
	#print "location_tabu_list",len(location_tabu_list)
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

def update_robust_obj(Kset,optK,objK):
	global biobjective
	global objective
	global objective_fcost
	biobjective=0.0
	objective_fcost=0.0
	if fixed_cost_obj==1:
		objective_fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)

	K=len(Kset)
	for k in range(K):
		obj= objective_fcost 
		for i in range(num_units):
			j=node_groups[i]
			obj+= nodedij[i][j]*Kset[k][i]
		objK[k]=obj
	objective=max(objK)-objective_fcost
	biobjective=max(objK[k]-optK[k] for k in range(K))
	#print biobjective,objective,objective_fcost

#solve scenario-based robust_pmp, robust_uflp
def ils_robust_uflp_pmp_kset(numf,Kset,optK):
	global best_biobjective_global
	global biobjective
	global objective
	global objective_fcost
	global node_groups
	global centersID
	global district_info
	global all_solutions
	global max_num_facility
	max_num_facility=numf
	initialize_instance()
	all_solutions=[]
	region_pool=[]
	t=time.time()
	ga_time=0.0
	biobjective= MAXNUMBER
	best_biobjective_global = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	K=len(Kset)
	Facility2List=[-1 for x in range(num_units)] 
	gainList=[[0.0 for x in range(num_districts)] for y in range(K)]#gian(fi)
	lossList=[[0.0 for x in range(num_districts)] for y in range(K)]#loss(fr)
	extraList=[[[0.0 for x in range(num_districts)] for y in range(num_districts)] for z in range(K)]#extra( fi, fr)
	objK=[0.0 for z in range(K)]

	t_ga=time.time()
	for idx in range(multi_start_count):
		n=max_num_facility
		if adaptive_number_of_facilities==1:
			n=max(5,num_districts/15)
			add=[-2,-1,-1,0,0,0,1,1,2]                
			random.shuffle(add) 
			n+=add[0]
		clist=range(num_districts)
		random.shuffle(clist)
		clist=clist[:n]
		centersID=[-1 for x in range(num_districts)]
		for x in clist: centersID[x]=x
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break            
		update_robust_obj(Kset,optK,objK)
		#print  [int(x) for x in objK]       
		nf2=sum(1 for x in centersID if x>=0)
		sta=1#robust_Renato_update(Facility2List,gainList,lossList,extraList,Kset)
		robust_Renato_update(Facility2List,gainList,lossList,extraList,Kset)        
		while sta==1:
			sta=robust_pmp_Renato(Facility2List,gainList,lossList,extraList,Kset,optK,objK)
		update_robust_obj(Kset,optK,objK)
		update_best_solution()

		'''biobjective=0.0
		objective_fcost=0.0
		if fixed_cost_obj==1:
			objective_fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		objective=0.0
		for j in range(num_units):
			i=node_groups[j]
			objective+=sum(nodedij[j][i]*Kset(k)*Pk[k] for k in range(K))     
		biobjective=objective+objective_fcost'''
		all_solutions.append([biobjective,centersID[:],node_groups[:]])
		nf=sum(1 for x in centersID if x>=0)
		print "init solution", idx, nf2,nf,biobjective,objective,time.time()-t_ga
	not_improved_global=0
	population=all_solutions
	population.sort(key=lambda x:x[0])
	if numf==1: return []

	improved_time=time.time()
	loop=-1
	while 1:
		if not_improved_global >= max_loops_solution_not_improved: break
		loop+=1
		r=random.random()
		sidx = int(min(multi_start_count,len(population))* pow(r,1.5)*0.999)
		r=random.random()
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_robust_obj(Kset,optK,objK)
		current=" current: " +str(int(population[sidx][0]))+" -> "
		not_improved_global+=1
		old_ids=centersID[:]
		best_obj=best_biobjective_global
		cur_obj=biobjective
		strength=3
		while 1:
			nf=sum(1 for x in centersID if x>=0)
			if nf<4: break            
			strategy=[[2,1],[2,3],[2,2],[3,2],[3,3],[3,4],[4,3],[4,4],[4,5]]
			if adaptive_number_of_facilities==0:
				maxStrength=max(4, int(nf*ruin_percentage+50)/100)
				maxStrength=min(8,maxStrength)
				strength=random.randint(3,maxStrength)
				strategy=[[strength,strength]]
			idx=random.randint(0,len(strategy)-1)
			strength=sum(strategy[idx])
			clist=[x for x in range(num_districts) if centersID[x]<0]
			if len(clist)<=strategy[idx][0]: continue
			random.shuffle(clist)
			for x in range(strategy[idx][0]):
				k=clist[x]
				centersID[k]=facilityCandidate[k]
			clist=[x for x in range(num_districts) if centersID[x]>=0]
			if len(clist)<=strategy[idx][1]: continue
			random.shuffle(clist)
			for x in range(strategy[idx][1]):
				k=clist[x]
				centersID[k]=-1
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]>=0:
						node_groups[i]=k
						break
			break
		fcost =sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		update_robust_obj(Kset,optK,objK)
		robust_Renato_update(Facility2List,gainList,lossList,extraList,Kset)
		rr_obj=biobjective
		sta=1
		while sta==1:
			sta=robust_pmp_Renato(Facility2List,gainList,lossList,extraList,Kset,optK,objK)#tested
			print ">",
		print
		update_robust_obj(Kset,optK,objK)
		update_best_solution()
	
		s=""
		if biobjective<best_obj:  #0.1%
			s="*"
			impp=((biobjective-best_obj)/biobjective)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		elif biobjective<cur_obj: 
			s="#"
		else: 
			s="-" 
		population.append([biobjective,centersID[:],node_groups[:]])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		if len(population)>max(10, multi_start_count*2):
			population.pop()
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Search loop "+str(loop) + " best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "
		nf=sum(1 for x in centersID if x>=0)
		s+=current + str(nf)+" "+str(int(biobjective))+" "+str(int(objective_fcost))
		s+= " Info: " +str(len(population))+" " +str(not_improved_global)+ " "+str(int(time.time()-t_ga))
		s+= " Imp: "+ str(strength)+":"+str(int(biobjective-cur_obj))
		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		#while len(population)>multi_start_count*5:
		#    population.pop()
		all_solutions=population
		if time.time()-t_ga > heuristic_time_limit:  break
		if stop_searching==1: break
		#print check_current_solution_continuality_feasibility()
	#post procedure
	population.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #population[0][2][:]
	centersID=best_centersID_global[:]
	update_robust_obj(Kset,optK,objK)
	
	ga_time=time.time()-t_ga
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	population.sort(key=lambda x:x[0])
	all_solutions=population
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]


#solve pmp, melp, mdelp, uflp, ce-uflp
def ils_pmp_envy(numf):
	global best_biobjective_global
	global node_groups
	global centersID
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	global max_num_facility
	max_num_facility=numf
	initialize_instance()
	all_solutions=[]
	region_pool=[]
	t=time.time()
	ga_time=0.0
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[]
	if is_spp_modeling>=1:
		pool_index=[[] for x in range(num_districts)]
	t_ga=time.time()
	
	for idx in range(multi_start_count):
		best_biobjective = MAXNUMBER
		if adaptive_number_of_facilities==1:
			n=max(5,num_districts/15)
			if max_facility_cost>0:
				n=int(max_facility_cost*num_districts/sum(facilityCost))
			add=[-2,-1,-1,0,0,0,1,1,2]                
			random.shuffle(add) 
			clist=range(num_districts)
			random.shuffle(clist)
			clist=clist[:n+add[0]]
			centersID=[-1 for x in range(num_districts)]
			for x in clist: centersID[x]=x
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]>=0:
						node_groups[i]=k
						break            
			update_envy_district_info()
			all_solutions.append([biobjective,centersID[:],node_groups[:]])
		if adaptive_number_of_facilities==0:
			ulist=[]
			sample_size=min(num_units,30*max_num_facility)
			while len(ulist)<sample_size: 
				u=random.randint(0,num_units-1)
				if u not in ulist: ulist.append(u)
			random.shuffle(ulist)
			obj,centers=k_medoids_sampling(ulist,[])
			if len(centers)!=numf: 
				print "error in generating initial solution...",len(centers)
				continue
			centersID=[-1 for x in range(num_units)]
		
			for x in centers: centersID[x]=facilityCandidate[x]
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					node_groups[i]=k
					break
		if spatial_contiguity==1:
			repair_fragmented_solution()
		nf2=sum(1 for x in centersID if x>=0)
		update_envy_district_info()
		update_best_solution()
		for i in range(20):
			sta=pmp_Whitaker()
			update_envy_district_info()
			update_best_solution()
			update_region_pool_all()
			if sta!=1:break
		all_solutions.append([biobjective,centersID[:],node_groups[:]])
		nf=sum(1 for x in centersID if x>=0)
		print "init solution", idx, nf2,nf,biobjective,objective
	not_improved_global=0
	population=all_solutions
	improved_time=time.time()
	loop=-1
	while 1:
		loop+=1
		r=random.random()
		sidx = int(min(multi_start_count,len(population))* pow(r,1.5)*0.999)
		r=random.random()
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_envy_district_info()
		current=" current: " +str(int(population[sidx][0]))+" -> "
		not_improved_global+=1
		old_ids=centersID[:]
		best_obj=best_biobjective_global
		cur_obj=biobjective
		
		strength=3
		if adaptive_number_of_facilities==0:
			strength=2
			maxStrength=2
			if max_num_facility >= 20:
				maxStrength=min(4, int(max_num_facility+10)/10)
				maxStrength=3
			strength=random.randint(2,maxStrength)
			print strength,
			assign_ruin_recreate_pmp_envy(strength)
		#uflp_shuffle()
		if adaptive_number_of_facilities==1:
			strategy=[[0,0],[0,1],[1,0],[1,1]] 
			strategy=[[2,1],[2,3],[2,2]]
			idx=random.randint(0,len(strategy)-1)
			strength=sum(strategy[idx])
			clist=[x for x in range(num_districts) if centersID[x]<0]
			if len(clist)<=strategy[idx][0]: continue
			random.shuffle(clist)
			for x in range(strategy[idx][0]):
				k=clist[x]
				centersID[k]=facilityCandidate[k]
				for i in range(num_units):
					k1=node_groups[i]
					if nodedij[i][k1]>nodedij[i][k]:
						node_groups[x]=k
			clist=[x for x in range(num_districts) if centersID[x]>=0]
			random.shuffle(clist)
			for x in range(strategy[idx][1]):
				k=clist[x]
				centersID[k]=-1
				ulist=[y for y in range(num_units) if node_groups[y]==k]
				for i in ulist:
					for k in NearFacilityList[i]:
						if centersID[k]>=0:
							node_groups[i]=k
							break
			update_envy_district_info()
		#end if uflp suffule        
		if spatial_contiguity==1:
			repair_fragmented_solution()
		imploop=max(10,strength*5)
		#imploop=100 
		rr_obj=biobjective
		for idx in range(imploop):
			if adaptive_number_of_facilities==10:   
				sta=pmp_uflp_TB()
			else:
				sta=pmp_Whitaker()
			#sta=pmp_Whitaker()
			'''for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k] >=0:
						node_groups[i]=k
						break'''
			update_envy_district_info()
			update_best_solution()
			update_region_pool_all()
			if sta!=1:
				#print idx,
				break
			#print i,sta,int(biobjective), int(objective),int(objective_fcost)
		print idx,
		if adaptive_number_of_facilities==0: update_center_pmp_envy()
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_envy_district_info()
		update_best_solution()
		update_region_pool_all()
			
		s=""
		if biobjective<best_obj:  #0.1%
			#del population[sidx]
			s="*"
			impp=((biobjective-best_obj)/biobjective)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
			#population.append([biobjective,centersID[:],node_groups[:]])
		elif biobjective<cur_obj: 
			#del population[sidx]
			s="#"
			#population.append([biobjective,centersID[:],node_groups[:]])
		else: 
			s="-" 
			#del population[sidx]
		population.append([biobjective,centersID[:],node_groups[:]])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		if len(population)>max(10, multi_start_count*2):
			population.pop()
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Search loop "+str(loop) + " best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))
		nf=sum(1 for x in centersID if x>=0)
		s+=current + str(nf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_fcost))
		s+= " Info: " +str(len(population))+" " +str(not_improved_global)+ " "+str(int(time.time()-t_ga))
		s+= " Imp: "+ str(int(biobjective-rr_obj))
		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		#while len(population)>multi_start_count*5:
		#    population.pop()
		all_solutions=population
		if time.time()-t_ga > heuristic_time_limit:  break
	#post procedure

	population.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #population[0][2][:]
	centersID=best_centersID_global[:]
	update_envy_district_info()
	ga_time=time.time()-t_ga
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sppmodel((time.time()-t_ga)/10,0.000001)
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break
		update_envy_district_info()
		#update_centers()
		update_best_solution()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		print "spp solution:",biobjective,objective_fcost,objective,objective_overload,time.time()-t_spp, time.time()-t_spp
		update_best_solution()
		node_groups=best_solution_global[:] #population[0][2][:]
		centersID=best_centersID_global[:]
		update_envy_district_info()

	print "final solution:",biobjective,objective_fcost,objective,objective_overload
	population.sort(key=lambda x:x[0])
	all_solutions=population
	#sta=check_solution_continuality_feasibility(node_groups)
	#print "Areal continuality(1 yes, 0 no):",sta
	#if spatial_contiguity==1:
	#    if sta==0:    return "infeasible final solution: continuality"
	##noprint "time",time.time()-t
	#search_stat()
	#print "location_tabu_list",len(location_tabu_list)
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]

def pmp_sampling_solution(psize,sample_size):
	global node_groups
	global centersID
	global all_solutions
	t=time.time()
	print "psize,sample_size",psize,sample_size
	idx=0
	while 1: #for idx in range(psize):
		best_biobjective = MAXNUMBER
		random.seed(seed+idx*100)
		ulist=[]
		if sample_size==num_units: ulist=range(num_units)
		else:
			while len(ulist)<sample_size: 
				u=random.randint(0,num_units-1)
				if u not in ulist: ulist.append(u)
		# find k_medoids
		random.shuffle(ulist)
		obj,centers=k_medoids_sampling(ulist,[])
		loop=0
		for x in centers: 
			if node_groups[x]!=x:
				node_groups[x]=x
		# #improve by TB method
		# while loop<max_num_facility:
			# loop+=1
			# random.shuffle(centers)
			# random.shuffle(ulist)
			# sta,obj,centers=r_r_reselect_location_homoDP(centers,ulist,ulist)
			# #print "multi_start",multi_start,loop,obj,time.time()-ga_time
			# if sta<=0: break
		#initial solution
		#print centers
		centersID=[-1 for x in range(num_units)]
		for x in centers: centersID[x]=x
		obj=0.0
		for i in range(num_units):
			bestd=MAXNUMBER
			bestk=-1
			for k in centers:
				if nodedik[i][k]<bestd:
					bestd=nodedik[i][k]
					bestk=k
			node_groups[i]=bestk
			obj+=bestd
		update_district_info()
		location_check(0)
		if spatial_contiguity>=1:
			repair_fragmented_solution_large_instance()
		update_district_info()
		#update_centers()
		klist=[x for x in range(num_districts) if centersID[x]>=0]
		if len(klist)<max_num_facility: continue
		sta=1
		for k in klist:
			if k not in node_groups:
				sta=0
				break
		'''total_area=sum(x[3] for x in nodes)
		for k in range(num_districts):
			if centersID[k]<0: continue
			ulist=[x for x in range(num_units) if node_groups[x]==k]
			area=sum(nodes[x][3] for x in ulist)
			if area<total_area*spatial_contiguity_minimum_percentage/max_num_facility/10000:
				sta=0
				break                '''
		if sta==0: continue        
		location_check(0)

		all_solutions.append([objective,centersID[:],node_groups[:]])
		#update_best_solution()
		idx+=1
		print "init. solution",idx,biobjective,objective,objective_overload,time.time()-t
		#print [x for x in centersID if x>=0]
		if len(all_solutions)>=psize: break
	#return all_solutions

def search_stat():
	arcpy_print("----------------search statistics----------------------")
	arcpy_print("one unit move, move and time: "+ str(count_op[0])+ ", " +str(time_op[0]) )
	arcpy_print("two unit move, move and time: "+ str(count_op[1])+ ", " +str(time_op[1]) )
	arcpy_print("three unit move, move and time: "+ str(count_op[2])+ ", " +str(time_op[2]) )
	arcpy_print("location subproblem time: "+ str(time_LNS1) )
	arcpy_print("reassign subproblem time: "+ str(time_LNS2) )
	arcpy_print("location swap time: "+ str(time_location[0]) )
	arcpy_print("location drop time: "+ str(time_location[1]) )
	arcpy_print("location add time: "+ str(time_location[2]) )
	arcpy_print("location add-drop time: "+ str(time_location[3]) )
	arcpy_print("location multi-exchange time: "+ str(time_location[4]) )
	arcpy_print("r_r_reselect_location_pmp time: "+ str(time_location[5]) )
	arcpy_print("location TB heur. time: "+ str(time_location[7]) )
	arcpy_print("TB_Whitaker time: "+str(time_Whitaker))
	arcpy_print("location PMP sub_mip time: "+ str(time_location[8]) )
	arcpy_print("location CFLP sub_mip time: "+ str(time_location[9]) )
	arcpy_print("location PMP TB time: "+ str(time_pmp_re_location) )
	arcpy_print("repair time: "+ str(time_repair) )
	arcpy_print("check edge unit time: "+str(time_check_edge_unit))
	arcpy_print("update_centers time: "+ str(time_update_centers) )
	arcpy_print("spp regions: "+ str(len(region_pool)) )
	arcpy_print("spp pooling time: "+ str(time_spp) )
	arcpy_print("connectivity check time: "+ str(time_check))
	arcpy_print("time for ruin and recreate: " + str(time_ruin_recreate))
	#if spatial_contiguity==1:
	#    sta=check_solution_continuality_feasibility(best_solution_global)
	#    arcpy_print("solution on continuality (0 no, 1 yes) : "+str(sta))
	arcpy_print("----------------end of search statistics----------------")
 
def sa(timelimit,loops,spp, myseed):
	global multi_start_count
	global SA_maxloops
	global seed
	global acceptanceRule
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global objective
	global biobjective
	global objective_overload
	global SA_temperature
	global SA_coolingrate
	global deviation
	global node_groups
	global centersID
	global region_pool
	global pool_index
	global is_spp_modeling
	global all_solutions
	global best_solution
	global best_centersID
	global operators_selected
	global last_loop_obj
	initialize_instance()
	#obj=location_model_lp(max_num_facility)
	#update_district_info()
	###noprint "obj and facilities",obj,len(centersID),centersID
	if mip_solver not in mip_solvers: is_spp_modeling=-1
	seed=myseed
	SA_maxloops=loops
	is_spp_modeling=spp
	init_temperature=1.0
	if seed<0:
		seed=random.randint(0,100)
	region_pool=[]
	all_solutions=[]
	t=time.time()
	best_biobjective = MAXNUMBER
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	best_objective = MAXNUMBER
	best_objective_overload = MAXNUMBER
	last_loop_obj = MAXNUMBER
	pool_index=[[] for x in range(max_num_facility)]
	solutions=[]
	best_solution=[] 
	best_centersID=[]
	move_count=0
	t_begin=time.time()
	t_h=time.time()
	#initial solutions as population
	not_improve=0
	not_improve_best=0
	idx=0
	for idx in range(multi_start_count):
		random.seed(seed*100+idx)
		not_improve_best=0
		if idx>=0:
			best_biobjective=MAXNUMBER
			acceptanceRule="hc" 
			initial_solution(idx)
			update_district_info()
			update_best_solution()
			VND_local_search()
			acceptanceRule="sa" 
		for loop in range (SA_maxloops):
			SA_coolingrate=math.exp( math.log(0.01)/SA_maxloops)
			SA_temperature=init_temperature*pow(SA_coolingrate,loop)
			#node_groups=best_solution[:]
			#update_district_info()
			last_loop_obj=best_biobjective
			obj=best_biobjective
			m=0
			#print int(biobjective),
			while 1:
				acceptanceRule="sa"#"rrt"# 
				RRT_local_search()
				acceptanceRule="hc" 
				RRT_local_search()
				#print ".",
				#print int(biobjective),
				m+=1
				if best_biobjective<obj: 
					obj=best_biobjective
					m=0
				if m==4: break
			update_region_pool_all()
			s=acceptanceRule +" start "+str(idx) +" loop " +str(loop)+ " best: " +str(int(best_biobjective_global))
			s+=" current: "+str(int(best_biobjective)) + " " + str(int(biobjective))
			s+=" "+str(SA_temperature)
			arcpy_print(s)
		all_solutions.append([best_biobjective,best_centersID[:],best_solution[:]])
		if time.time()-t_h > heuristic_time_limit: break
		if idx>=multi_start_count: break 
	node_groups=best_solution_global[:]
	update_district_info()
	update_best_solution()
	update_region_pool_all()
	all_solutions.sort(key=lambda x:x[0])
	if is_spp_modeling>=1:
		arcpy_print("spp modeling ...")
		if sppmodel(heuristic_time_limit,0.0001)>=0:
			update_district_info()
			update_best_solution()
			all_solutions.append([best_biobjective,best_centersID[:],best_solution[:]])
	if spatial_contiguity==1  and check_solution_continuality_feasibility(best_solution_global)==0:
		return "infeasible solution on continuality"
	all_solutions.sort(key=lambda x:x[0])
	search_stat()
	return [best_biobjective_global, best_objective_global, best_overload_global, best_solution_global]

		

# return k centers by k-means
def k_medoids_cflpr_sampling(num_k):
	global centersID
	global node_groups
	centers=[]
	sol=[-1 for x in range(num_units)]
	distance_obj=0.0
	while 1:
		if len(centers)==num_k: break
		k=random.randint(0,num_districts-1)
		if k not in centers: centers.append(k)
	#for i in range(num_units):
	#    for k in NearFacilityList[i]:
	#        if k in centers:
	#            distance_obj+=nodedik[i][k]
	#            sol[i]=k
	#            break
	centers2=[]
	sol2=[-1 for x in range(num_units)]
	distance_obj2=0.0
	loop=0
	#k-means
	while 1:
		loop+=1
		distance_obj=0.0
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if k in centers:
					sol[i]=k
					distance_obj+=nodedik[i][k]
					break
		distance_obj2=0.0
		centers2=[]
		for k in centers:
			ulist=[x for x in range(num_units) if sol[x]==k]
			if len(ulist)==0: continue
			clist=range(num_districts)
			cid=-1
			mindis=MAXNUMBER
			for i in clist:
				dsum=sum(nodedik[x][i] for x in ulist)
				if dsum<mindis:
					mindis=dsum
					cid=i
			centers2.append(cid)
			distance_obj2+=mindis
			for i in ulist: sol2[i]=cid
		sol=sol2[:]
		centers=list(set(centers2))
		#print distance_obj,distance_obj2
		if abs(distance_obj2-distance_obj)/distance_obj<0.0001:
			break
	return centers

#method
#0 basic 2SFCA: 0, na,na
#1 gravity 2SFCA: 1,1.0,2.0
#2 Gaussian 2SFCA: 2,1.0,na
#3 Kernel Density 2SFCA, 3,1.0,na
#4 OSD
def spatial_accessibility(method,radius,beta):
	#global node_groups
	#global centersID
	#centersID=facilityCandidate
	#node_groups=[-1 for x in range(num_units)]
	t=time.time()
	rlist=[0.0 for x in range(num_districts)]
	for k in range(num_districts):
		dk=0.0
		for i in nearCustomers[k]:
			if nodedij[i][k]>radius: break
			if method==0: dk+=nodes[i][3]
			if method==1: dk+=nodes[i][3]/pow(nodedij[i][k],beta)
			if method==2: dk+=nodes[i][3]* ( math.exp(-nodedij[i][k]*nodedij[i][k]/radius/radius/2)-math.exp(-0.5) )/ ( 1-math.exp(-0.5) )
			if method==3: dk+=nodes[i][3]*(0.75 - 0.75*nodedij[i][k]*nodedij[i][k]/radius/radius ) 
		if dk>0.0000001: rlist[k]=facilityCapacity[k]/dk
	alist=[0.0 for x in range(num_units)]
	for i in range(num_units):
		a=0.0
		for k in NearFacilityList[i]:
			if nodedij[i][k]>radius: break
			if method==0: a+=rlist[k]
			if method==1: a+=rlist[k]/pow(nodedij[i][k],beta)
			if method==2: a+=rlist[k]* ( math.exp(-nodedij[i][k]*nodedij[i][k]/radius/radius/2)-math.exp(-0.5) )/ ( 1-math.exp(-0.5) )
			if method==3: a+=rlist[k]*(0.75 - 0.75*nodedij[i][k]*nodedij[i][k]/radius/radius) 
		alist[i]=a
	print "----------spatial_accessibility-------------"
	print "method, radius, beta", method,radius,beta
	print "time",time.time()-t
	print "Idx x y D ID S r1 r2 A Dis"
	for i in range(num_units):
		#k=NearFacilityList[i][0]
		if nodes[i][3]<=0: continue
		#node_groups[i]=k
		for x in nodes[i]: print x,
		k=node_groups[i]
		print alist[i],nodedij[i][k]
	print "time",time.time()-t
	print "----------stat-------------------"
	pop=[0,0,0,0,0]
	for i in range(num_units):
		a=alist[i]
		if a<0.6: 
			 pop[0]+=nodes[i][3]
		elif a<0.8: 
			 pop[1]+=nodes[i][3]
		elif a<1.2: 
			 pop[2]+=nodes[i][3]
		elif a<1.4: 
			 pop[3]+=nodes[i][3]
		else: 
			 pop[4]+=nodes[i][3]
	print "time",time.time()-t
	for x in pop: print x*10000/total_pop/100.0, 
	print "time",time.time()-t
	update_district_info()
	m=print_equality_measures()
	for x in m: print x,m[x]

def print_equality_measures():
	#print "-----------equality measures---------------"
	update_district_info()
	maxd=0.0
	mind=MAXNUMBER
	maxdev=0.0
	avgd=objective/total_pop
	absdev=0.0
	stddev=0.0
	Theil=0.0
	schutz=0.0
	upperVar=0.0
	lowerVar=0.0
	upperVarD=0.0
	lowerVarD=0.0
	upperMad=0.0
	for i in range(num_units): 
		k=node_groups[i]
		dis=nodedij[i][k]
		w=nodes[i][3]
		absdev+=w*abs(dis-avgd)
		stddev+=w*(dis-avgd)*(dis-avgd)
		if dis>maxd: maxd=dis
		if dis<mind: mind=dis
		if abs(dis-avgd)>maxdev: maxdev=abs(dis-avgd)
		'''if dis>0:
			a=dis*math.log(dis)-avgd*math.log(avgd)
			Theil+=w*a*a
		else:
			a=avgd*math.log(avgd)
			Theil+=w*a*a'''
		if dis>0:
			a=math.log(dis/avgd)
			Theil+=w*dis*a
		schutz+=w*abs(dis-avgd)
		if dis>avgd:
			upperVar+=w*(dis-avgd)*(dis-avgd)
			#upperVarD+=w*(dis-envy_service_distance)*(dis-envy_service_distance)
			upperMad+=w*(dis-avgd)
		else:
			lowerVar+=w*(dis-avgd)*(dis-avgd)
			#lowerVarD+=w*(dis-envy_service_distance)*(dis-envy_service_distance)
	equality_measures={}
	equality_measures["Max"]= maxd
	equality_measures["Range"]=maxd-mind
	equality_measures["Mean"]=avgd
	equality_measures["StdDev"]=math.sqrt(stddev/total_pop)
	#equality_measures["MaxDev"]=maxdev
	equality_measures["MAD"]=absdev/total_pop
	#equality_measures["Varance"]=stddev/total_pop
   
	Gini=0.0
	for i in range(num_units): 
		k=node_groups[i]
		d1=nodedij[i][k]
		w1=nodes[i][3]
		for j in range(num_units): 
		   k=node_groups[j]
		   d2=nodedij[j][k]
		   w2=nodes[j][3]
		   Gini+=w1*w2*abs(d1-d2)
	#print "Gini",Gini/total_pop/total_pop/2/avgd #Gini/d.num_units/d.num_units/2/avgd
	equality_measures["meanAD"]=Gini/total_pop/total_pop
	equality_measures["CV"]=equality_measures["StdDev"] /avgd
	equality_measures["SchutzI"]=schutz/total_pop/2/avgd
	equality_measures["Gini"]=Gini/total_pop/total_pop/2/avgd
	equality_measures["Theil"]= Theil/avgd/total_pop
	equality_measures["lowerVar"]=lowerVar
	#equality_measures["lowerVar2"]=lowerVarD
	equality_measures["upperVar"]=upperVar
	#equality_measures["upperVar2"]=upperVarD
	equality_measures["upperMad"]=upperMad*2/total_pop
	return equality_measures

def EDE_distance(beta):
	sum1=0.0
	sum2=0.0
	for i in range(num_units): 
		k=node_groups[i]
		d=nodedij[i][k]
		w=nodes[i][3]
		sum1+=w*d
		sum2+=w*d*d
	alpha=sum1/sum2*beta
	ede=0.0
	for i in range(num_units): 
		k=node_groups[i]
		d=nodedij[i][k]
		w=nodes[i][3]
		ede+=w*math.exp(alpha*d)
	ede/=total_pop
	ede=math.log(ede)/alpha
	return sum1/sum2,ede
	

def coverage_stat2(dlist):
	covered=[0 for x in range(len(dlist))]
	for i in range(num_units):
		k=node_groups[i]
		dis=nodedij[i][k]
		demand=nodes[i][3]
		for j in range(len(dlist)):
			if dis<=dlist[j]: covered[j]+=demand
	for i in range(len(dlist)):
		if covered[i]>0:
			print dlist[i],int(covered[i]*10000.0/total_pop)/100.0

def coverage_stat():
	maxd=0.0
	for i in range(num_units): 
		k=node_groups[i]
		dis=nodedij[i][k]
		if dis>maxd: maxd=dis
	covered=[0 for x in range(20)]
	dlist=[0.5*x for x in range(20)]
	for i in range(num_units):
		k=node_groups[i]
		dis=nodedij[i][k]
		demand=nodes[i][3]
		for j in range(20):
			if dis<=dlist[j]: covered[j]+=demand
	#print dlist
	#print covered
	#print [x*100.0/total_pop for x in covered]
	for i in range(len(dlist)):
		#if covered==total_pop: break
		print dlist[i],int(covered[i]*10000.0/total_pop)/100.0
		if dlist[i]>maxd: break

def PMP_and_minvar_2sfca(num_f,radius,supply_all):
	#pmp_mip_model(num_f,radius,cover_percent,time_limit,mipgap)
	#pmp_mip_model(num_f,20,100,1000,0.000001)
	#Li et al. 2022, CEUS
	#MALP
	beta=0.01
	facilityList=[x for x in range(num_districts) if centersID[x]>=0]
	print "facility locations:",facilityList
	print "facility idx",[x for x in centersID if x>=0]
	fik=[ [0.0 for x in range(num_f) ] for y in range(num_units)]
	for i in range(num_units):
		for k in range(num_f):
			j=facilityList[k]
			d=nodedij[i][j]
			if d>radius: continue
			fik[i][k]= ( math.exp(-d*d/radius/radius/2)-math.exp(-0.5) )/( 1-math.exp(-0.5))
			#print [i,k,fik[i][k]],
	#print "fik", fik[500:700]

	glist=[100000.0 for x in range(num_f)]
	for k in range(num_f):
		g=sum(nodes[i][3]* fik[i][k] for i in range(num_units))
		glist[k]=1.0/g    
	#print "glist",glist
	
	dlist=[nodes[x][3] for x in range(num_units)]
	#print "dlist",dlist
	
	#P=FG, H=PDP, Q=-PDA
	pik=[ [0.0 for x in range(num_f) ] for y in range(num_units)]
	for i in range(num_units):
		for k in range(num_f):
			pik[i][k]=fik[i][k]*glist[k]
	#print "pik",pik[:200]

	hlist=[0.0 for k in range(num_f)]
	for k in range(num_f):
		hlist[k]=sum( pik[i][k] * pik[i][k] *dlist[i] for i in range(num_units))  
	#print "hlist",hlist

	qlist=[0.0 for k in range(num_f)]
	a=supply_all*1.0/total_pop
	for k in range(num_f):
		qlist[k]=sum( a*dlist[i]*pik[i][k] for i in range(num_units))
	#print "qlist",qlist

	f = open("pmp_2sfca_"+str(num_f)+"_"+str(radius)+"_"+str(supply_all)+".lp","w")
	f.write("minimize\nobj: ")
	
	s=""
	f.write(" [ ")
	for k in range(num_f):
		s += str(0.5*hlist[k])+ " x_" +str(k)+" ^ 2 + " 
	f.write( s[:-3]+ " ] / 2 ")

	s=""
	for k in range(num_f):
		s+= " - " + str(qlist[k])+ " x_" +str(k) 
	f.write( s +"\n")
	f.write("subject to\n")
	s="_c1: "
	for k in range(num_f):
		s += " x_" +str(k)+" + "
	f.write(s[:-3]+ " <= " + str(supply_all)+"\n")
	f.write("generals\n")
	for k in range(num_f):
		s = " x_" +str(k)+"\n"
		f.write(s)
	f.write("end\n")
	f.close()    

def Minvar_2sfca(num_f,radius,supply_all):
	#pmp_mip_model(num_f,radius,cover_percent,time_limit,mipgap)
	#pmp_mip_model(num_f,20,100,1000,0.000001)
	#Li et al. 2022, CEUS
	#MALP
	beta=0.01
	facilityList=[x for x in range(num_districts) if centersID[x]>=0]
	print "facility locations:",facilityList
	print "facility idx",[x for x in centersID if x>=0]
	fik=[ [0.0 for x in range(num_f) ] for y in range(num_units)]
	for i in range(num_units):
		for k in range(num_f):
			j=facilityList[k]
			d=nodedij[i][j]
			#if d>radius: continue
			fik[i][k]= math.exp(-d*beta)
			#print [i,k,fik[i][k]],
	#print "fik", fik[500:700]

	glist=[100000.0 for x in range(num_f)]
	for k in range(num_f):
		g=sum(nodes[i][3]* fik[i][k] for i in range(num_units))
		glist[k]=1.0/g    
	#print "glist",glist
	
	dlist=[nodes[x][3] for x in range(num_units)]
	#print "dlist",dlist
	
	#P=FG, H=PDP, Q=-PDA
	pik=[ [0.0 for x in range(num_f) ] for y in range(num_units)]
	for i in range(num_units):
		for k in range(num_f):
			pik[i][k]=fik[i][k]*glist[k]
	#print "pik",pik[:200]

	hlist=[0.0 for k in range(num_f)]
	for k in range(num_f):
		hlist[k]=sum( pik[i][k] * pik[i][k] *dlist[i] for i in range(num_units))  
	#print "hlist",hlist

	qlist=[0.0 for k in range(num_f)]
	a=supply_all*1.0/total_pop
	for k in range(num_f):
		qlist[k]=sum( a*dlist[i]*pik[i][k] for i in range(num_units))
	#print "qlist",qlist'''

	f = open("pmp_2sfca_"+str(num_f)+"_"+str(radius)+"_"+str(supply_all)+".lp","w")
	f.write("minimize\nobj: ")
	
	s=""
	f.write(" [ ")
	for k in range(num_f):
		s += str(hlist[k])+ " x_" +str(k)+" ^ 2 + " 
	f.write( s[:-3]+ " ] / 2 ")

	s=""
	for k in range(num_f):
		s+= " - " + str(qlist[k])+ " x_" +str(k) 
	f.write( s +"\n")
	f.write("subject to\n")
	s="_c1: "
	for k in range(num_f):
		s += " x_" +str(k)+" + "
	f.write(s[:-3]+ " = " + str(supply_all)+"\n")
	s="_c1: a = " + str(a)
	f.write(s+"\n")

	f.write("generals\n")
	for k in range(num_f):
		s = " x_" +str(k)+"\n"
		f.write(s)
	f.write("end\n")
	f.close()    

def sol_stat():
	fcost=objective_fcost
	sol={}
	sol["num_facility"]=sum(1 for x in centersID if x>=0)
	sol["objective"]=biobjective
	sol["TotalCost"]=objective+fcost
	sol["DCost"]=objective
	sol["Fcost"]=fcost
	sol["Fsupply"]=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)
	sol["Overload"]=objective_overload
	sol["WeightedEnvyValue"]=objective_envy
	if objective_envy>0:
		sol["EnvyValue"]=objective_envy/envy_objective_weight
	else:
		envy=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envy+=nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
		sol["EnvyValue"]=envy
	sol["OverloadPenalty"]=int(objective_pentalty_on_overload/penalty_on_demand)
	sol["RMaxPenalty"]=int(objective_pentalty_on_rmax/penalty_on_demand)
	sol["RCoveragePenalty"]=int(objective_pentalty_on_covering/penalty_on_demand)
	if facilityMinimumCapacity>0:
		lowload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			lowload += max(0, facilityMinimumCapacity-district_info[k][1])
		sol["MinCap"]=lowload

	if facilityMaximumCapacity>0:
		overload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			overload += max(0, district_info[k][1]-facilityMaximumCapacity)
		sol["MaxCap"]=overload
	
	sol["Penalty"]=penalty_on_demand
	sol["MaxR2"]=cflp_max_service_radius
	sol["MaxR"]=cflp_service_radius_preference
	sol["MinRCover"]=cflp_min_service_coverage_percentage

	return sol
  
def check_sub(dlist,ulist,centers,exist_facility):
	for k in dlist:
		if centersID[k]<0: print k,"in dlist not used"
		if k not in centers: print k,"in dlist not in centers"
		if k in exist_facility: print k,"in dlist also in exist_facility"
	for i in ulist:
		if node_groups[i] not in dlist: print i, "in ulist not belongs dlist"
	for k in centers:
		if k not in dlist and centersID[k]>=0: print k, "in centers is open"
	for k in exist_facility:
		if centersID[k]<0: print k,"in exist_facility not used"
		if k in dlist: print k,"in exist_facility also in dlist"


# modified Horton et al(2025) A Scalable Optimization Approach for Equitable Facility Location
def EDE_model(capacity,num_f,mean,epsilon,time_limit,mipgap): 
	global centersID
	global node_groups
	prob = pulp.LpProblem("pmp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	xvariables={}
	xcost={}
	for i in ulist:
		for k in centers:
			xvariables["x_" +str(i)+"_"+str(k)]=pulp.LpVariable("x_" +str(i)+"_"+str(k), 0, 1, pulp.LpBinary)
			d=nodedij[i][k]
			if envy_service_objective==0:
				xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*d
			if envy_service_objective==1 and d>envy_service_distance:
				xcost["x_" +str(i)+"_"+str(k)]=travel_distance_weight*nodes[i][3]*d + nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if envy_service_objective==2 and d>envy_service_distance:
				xcost["x_" +str(i)+"_"+str(k)]=travel_distance_weight*nodes[i][3]*d + nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			if envy_service_objective==8:
				xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*pow(d,2)
			if envy_service_objective==9:
				xcost["x_" +str(i)+"_"+str(k)]=nodes[i][3]*math.exp(epsilon*d/mean)

	costs={}
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)

	obj=""
	for x in xvariables:
		obj +=xcost[x]* xvariables[x]
	prob += obj

	for i in ulist:
		s=""
		for k in centers:
			s+=xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s  == 1

	if num_f>0:
		s=""
		for k in centers:
			s+=yvariables["y_"+str(k)]
		prob +=s  == num_f
	if max_facility_cost>0:
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_"+str(k)]
		prob +=s  <= max_facility_cost
	if capacity==0:
		for k in centers:
			s=""
			for i in ulist:
				s+=xvariables["x_" +str(i)+"_"+str(k)]
			s-=num_units*yvariables["y_" + str(k)]
			prob +=s <= 0

		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	if capacity==1:
		for k in centers:
			s=""
			for i in ulist:
				s+=nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
			s-=facilityCapacity[k]*yvariables["y_" + str(k)]
			prob +=s <= 0
		for k in centers:
			for i in ulist:
				s=xvariables["x_" +str(i)+"_"+str(k)] -yvariables["y_" + str(k)]
				prob +=s <= 0
	
	prob.writeLP("_EDE.lp")
	initvalues=pmp_mst()
	for x,v in initvalues:
		 if x.find("x")==0:  xvariables[x].setInitialValue(v)
		 if x.find("y")==0:  yvariables[x].setInitialValue(v)
	warmStart=True
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, warmStart=True, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		##noprint "model unsolved..."
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			if items[0]=='z':
				continue
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				k=int(items[2])
				node_groups[i]=k
	if capacity==0:
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k] >=0:
					node_groups[i]=k
					break
	update_district_info()
	return 1

def UFLP_PMP_ILS(swapMethod):
	global nodedij
	global nodedik
	global node_groups
	global centersID
	global envy_service_objective
	global travel_distance_weight
	nodedij_org=copy.deepcopy(nodedij)
	nodedik_org=copy.deepcopy(nodedik)
	for i in range(num_units):
		for j in range(num_districts):
			d=nodedij[i][j]
			if envy_service_objective==1:
				d2=max(0,d-envy_service_distance)
				nodedij[i][j]=travel_distance_weight*d+envy_objective_weight*d2*d2
			if envy_service_objective==4:
				d2=max(0,d-envy_service_distance)
				nodedij[i][j]=travel_distance_weight*d+envy_objective_weight*d2
			if envy_service_objective==7:
				nodedij[i][j]=d*d
			if envy_service_objective==8:
				nodedij[i][j]=math.exp(envy_objective_weight*d/envy_service_distance)
			nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	envy_service_objective_back=envy_service_objective
	travel_distance_weight_back=travel_distance_weight
	envy_service_objective=0
	travel_distance_weight=1
	#ils_pmp_envy(max_num_facility)
	ils_pmp_fast(max_num_facility,swapMethod)
	nodedij=nodedij_org
	nodedik=nodedik_org
	envy_service_objective=envy_service_objective_back
	travel_distance_weight=travel_distance_weight_back
	node_groups=best_solution_global
	centersID=best_centersID_global
	update_district_info()

def EDE_CEEFLP_MH(threshold_distance, alpha, psize,maxloops):
	global nodedij
	global nodedik
	global node_groups
	global centersID
	
	nodedij_org=copy.deepcopy(nodedij)
	nodedik_org=copy.deepcopy(nodedik)
	for i in range(num_units):
		for j in range(num_districts):
			d=nodedij[i][j]
			nodedij[i][j]=math.exp(alpha*d/threshold_distance)
			nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	#ils_pmp(nf,multistarts,7200,-1)
	cmdelp_matheuristic(100000.0,100000.0,0,psize,maxloops)
	nodedij=nodedij_org
	nodedik=nodedik_org
	node_groups=best_solution_global
	centersID=best_centersID_global
	update_district_info()

def EDE_CFLP_MH(psize,maxloops):
	global nodedij
	global nodedik
	global node_groups
	global centersID
	global envy_service_objective
	global envy_objective_weight
	global travel_distance_weight
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	print   "----------------original problem definition------------------"
	print   "envy_service_objective",envy_service_objective
	print   "envy_service_distance",envy_service_distance
	print   "envy_objective_weight",envy_objective_weight        
	print   "travel_distance_weight",travel_distance_weight
	print   "cflp_max_service_radius",cflp_max_service_radius
	print   "cflp_service_radius_preference",cflp_service_radius_preference
	
	print "Solving by distance equivilent problems... "
	if envy_service_objective>0:
		nodedij_org=copy.deepcopy(nodedij)
		nodedik_org=copy.deepcopy(nodedik)
		for i in range(num_units):
			for j in range(num_districts):
				d=nodedij[i][j]
				nodedij[i][j]=d*envy_objective_weight_of_travelcost
				#if d>cflp_max_service_radius: 
				#   nodedij[i][j]+=penalty_on_demand    
				if envy_service_objective==1:
					d2=max(0,d-envy_service_distance)
					nodedij[i][j]+=envy_objective_weight*d2*d2
				if envy_service_objective==4:
					d2=max(0,d-envy_service_distance)
					nodedij[i][j]+=envy_objective_weight*d2
				if envy_service_objective==8:
					nodedij[i][j]=d*d
				if envy_service_objective==9:
					nodedij[i][j]=math.exp(envy_objective_weight*d/envy_service_distance)
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
		envy_service_objective_back=envy_service_objective
		envy_objective_weight_back=envy_objective_weight
		travel_distance_weight_back=travel_distance_weight
		cflp_max_service_radius_back=cflp_max_service_radius
		cflp_service_radius_preference_back=cflp_service_radius_preference
		
		d2=max(0,cflp_max_service_radius-envy_service_distance)
		d1=max(0,cflp_service_radius_preference-envy_service_distance)
		if envy_service_objective==1:
			cflp_max_service_radius=cflp_max_service_radius*envy_objective_weight_of_travelcost + envy_objective_weight*d2*d2
			cflp_service_radius_preference=cflp_service_radius_preference*envy_objective_weight_of_travelcost + envy_objective_weight*d1*d1
		if envy_service_objective==4:
			cflp_max_service_radius=cflp_max_service_radius*envy_objective_weight_of_travelcost + envy_objective_weight*d2
			cflp_service_radius_preference=cflp_service_radius_preference*envy_objective_weight_of_travelcost + envy_objective_weight*d1
		if envy_service_objective==8:
			cflp_max_service_radius=cflp_max_service_radius*cflp_max_service_radius
			cflp_service_radius_preference=cflp_service_radius_preference*cflp_service_radius_preference
		if envy_service_objective==9:
			r2=cflp_max_service_radius
			r1=cflp_service_radius_preference
			cflp_max_service_radius=math.exp(r2/envy_service_distance)
			cflp_service_radius_preference=math.exp(r1/envy_service_distance)

		envy_service_objective=0
		envy_objective_weight=0        
		travel_distance_weight=1
	print   "----------------equivilent problem definition------------------"
	print   "envy_service_objective",envy_service_objective
	print   "envy_objective_weight",envy_objective_weight        
	print   "travel_distance_weight",travel_distance_weight
	print   "envy_service_objective",envy_service_objective
	print   "cflp_max_service_radius",cflp_max_service_radius
	print   "cflp_service_radius_preference",cflp_service_radius_preference
	print   "large_neigborhood_maxIJ",large_neigborhood_maxIJ
		
	if initial_solution_method<=9:
		cflpr_matheuristic(cflp_max_service_radius,cflp_service_radius_preference,cflp_min_service_coverage_percentage,psize,maxloops)
	else:
		cflpr_model(cflp_max_service_radius,cflp_service_radius_preference,cflp_min_service_coverage_percentage,max_num_facility,7200,0.0000000001)
		update_best_solution()        
		update_cflpr_district_info()
	if envy_service_objective_back>0:
		nodedij=nodedij_org
		nodedik=nodedik_org
		node_groups=best_solution_global
		centersID=best_centersID_global
		envy_service_objective=envy_service_objective_back
		envy_objective_weight=envy_objective_weight_back
		travel_distance_weight=travel_distance_weight_back
		cflp_max_service_radius=cflp_max_service_radius_back
		cflp_service_radius_preference=cflp_service_radius_preference_back
	update_cflpr_district_info()
	

def RobustCEECFLP_MH(ulevel, rlevel,psize,maxloops):
	global nodedij
	global nodedik
	global node_groups
	global centersID
	global envy_service_objective
	global envy_objective_weight
	global travel_distance_weight
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	initialize_instance()    
	print   "----------------original problem definition------------------"
	print   "envy_service_objective",envy_service_objective
	print   "envy_service_distance",envy_service_distance
	print   "envy_objective_weight",envy_objective_weight        
	print   "travel_distance_weight",travel_distance_weight
	print   "cflp_max_service_radius",cflp_max_service_radius
	print   "cflp_service_radius_preference",cflp_service_radius_preference
	
	print "Solving by distance equivilent problems... "
	nodedij_org=copy.deepcopy(nodedij)
	nodedik_org=copy.deepcopy(nodedik)
	for i in range(num_units):
		for j in range(num_districts):
				d=nodedij[i][j]
				nodedij[i][j]=d*travel_distance_weight
				d2=max(0,d-envy_service_distance)
				nodedij[i][j]+=envy_objective_weight*d2*d2
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]

	envy_service_objective_back=envy_service_objective
	envy_objective_weight_back=envy_objective_weight
	travel_distance_weight_back=travel_distance_weight
	envy_service_objective=0
	envy_objective_weight=0        
	travel_distance_weight=1

	print   "----------------equivilent problem definition------------------"
	print   "envy_service_objective",envy_service_objective
	print   "envy_objective_weight",envy_objective_weight        
	print   "travel_distance_weight",travel_distance_weight
	print   "envy_service_objective",envy_service_objective
	print   "cflp_max_service_radius",cflp_max_service_radius
	print   "cflp_service_radius_preference",cflp_service_radius_preference
	print   "large_neigborhood_maxIJ",large_neigborhood_maxIJ
		
	robustCFLP_matheuristic(ulevel, rlevel,psize,maxloops)
	nodedij=nodedij_org
	nodedik=nodedik_org
	node_groups=best_solution_global
	centersID=best_centersID_global
	envy_service_objective=envy_service_objective_back
	envy_objective_weight=envy_objective_weight_back
	travel_distance_weight=travel_distance_weight_back
	if envy_service_objective>0: update_cflpr_district_info()   
	else: update_rubust_district_info(ulevel, rlevel)

def RobustCEECFLP_Worst_MH(ulevel, rlevel,psize,maxloops):
	global nodedij
	global nodedik
	global nodes
	global node_groups
	global centersID
	global envy_service_objective
	global envy_objective_weight
	global travel_distance_weight
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	print   "----------------original problem definition------------------"
	print   "envy_service_objective",envy_service_objective
	print   "envy_service_distance",envy_service_distance
	print   "envy_objective_weight",envy_objective_weight        
	print   "travel_distance_weight",travel_distance_weight
	print   "cflp_max_service_radius",cflp_max_service_radius
	print   "cflp_service_radius_preference",cflp_service_radius_preference
	
	print "Solving by distance equivilent problems... "
	nodedij_org=copy.deepcopy(nodedij)
	nodedik_org=copy.deepcopy(nodedik)
	for i in range(num_units):
		for j in range(num_districts):
				d=nodedij[i][j]
				nodedij[i][j]=d*travel_distance_weight
				d2=max(0,d-envy_service_distance)
				nodedij[i][j]+=envy_objective_weight*d2*d2
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]

	envy_service_objective_back=envy_service_objective
	envy_objective_weight_back=envy_objective_weight
	travel_distance_weight_back=travel_distance_weight
	envy_service_objective=0
	envy_objective_weight=0        
	travel_distance_weight=1
	print   "----------------equivilent problem definition------------------"
	print   "envy_service_objective",envy_service_objective
	print   "envy_objective_weight",envy_objective_weight        
	print   "travel_distance_weight",travel_distance_weight
	print   "envy_service_objective",envy_service_objective
	print   "cflp_max_service_radius",cflp_max_service_radius
	print   "cflp_service_radius_preference",cflp_service_radius_preference
	print   "large_neigborhood_maxIJ",large_neigborhood_maxIJ
	
	damands=[nodes[x][3] for x in range(num_units)]
	za=0
	CDF=[0.5,0.5398,0.5793,0.6179,0.6554,0.6915,0.7257,0.758,0.7881,0.8159,
			0.8413,0.8643,0.8849,0.9032,0.9192,0.9332,0.9452,0.9554,0.9641,0.9713,
			0.9772,0.9821,0.9861,0.9893,0.9918,0.9938,0.9953,0.9965,0.9974,0.9981,
			0.9987,0.999,0.9993,0.9995,0.9997]    
	for idx in range(33):
		if rlevel<1-CDF[idx]:
			za=idx/10.0
	if za>1.732: za=1.732
	for i in range(num_units):
		nodes[i][3]+= za*nodes[i][3]*ulevel[i]/1.732
	#rlevel -> nodes
	cflpr_matheuristic(1000000.0,100000.0,0,psize,maxloops)
	#CFLP_matheuristic(,psize,maxloops)
	nodedij=nodedij_org
	nodedik=nodedik_org
	node_groups=best_solution_global
	centersID=best_centersID_global
	envy_service_objective=envy_service_objective_back
	envy_objective_weight=envy_objective_weight_back
	travel_distance_weight=travel_distance_weight_back
	for x in range(num_units):
		nodes[x][3]=demands[x]    
	if envy_service_objective>0: update_cflpr_district_info()   
	else: update_rubust_district_info(ulevel, rlevel)
	
def robustCFLP_matheuristic(ulevel, rlevel, psize,maxloops):
	global best_biobjective_global
	global node_groups
	global centersID
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	global max_loops_solution_not_improved
	global multi_start_count
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	global travel_distance_weight
	initialize_instance()    

	max_loops_solution_not_improved=maxloops
	multi_start_count=psize
	print "num_facility:",max_num_facility
	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	not_improved_global=0
	loops=multi_start_count

	for idx in range(loops):
		if initial_solution_method!=1:
			sta=drop_method_cflpr(10000.0,1.0,0)
		else:
			sta=cflpr_lp_model(10000,10000,0,max_num_facility,heuristic_time_limit/10,0.01)
		
		nf=sum(1 for x in centersID if x>=0)
		update_rubust_district_info(ulevel, rlevel)
		print "init. sol.",idx, "mthd",nf,biobjective,objective,objective_overload,time.time()-t
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		update_best_solution()

	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	print "pop size",len(population),"obj values: "+str(population[0][0])+"-"+str(population[-1][0])
	loop=-1
	
	while 1:
		r=random.random()
		sidx = int(min(multi_start_count-1,len(population))*pow(r,1.5)*0.999)
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_rubust_district_info(ulevel, rlevel)
		bnf=sum(1 for x in centersID if x>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(objective_overload)+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		gap=1.0e-10
		#if not_improved_global <= max_loops_solution_not_improved/2: gap=0.01
		sta=robust_sub_model(ulevel, rlevel, min(large_neigborhood_maxIJ/50,300), gap)
		location_check(1)
		update_rubust_district_info(ulevel, rlevel)

		location_check(5)
		update_best_solution()
		update_region_pool_all()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])

		
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		all_solutions=copy.deepcopy(population)
		s="" 
		if best_biobjective_global<obj-0.000001: 
			s+="*"
			impp=(best_biobjective_global-obj)/best_biobjective_global*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: 
			s+="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop) + " " +str(sta)+" Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(fc)+" "+str(int(objective_overload))
		s+=" Info: " +str(len(population))+" " + str(not_improved_global)+ " "+str(int(time.time()-t))

		arcpy_print(s)
		#print not_improved_global, max_loops_solution_not_improved
		if not_improved_global >= max_loops_solution_not_improved: break
		if stop_searching==1: break
		if time.time()-t>heuristic_time_limit: break

	node_groups=best_solution_global[:]
	centersID=best_centersID_global[:]
	update_rubust_district_info(ulevel, rlevel)
	nf=sum(1 for x in centersID if x>=0)
	print "Heuristic solution:",nf,biobjective,objective_fcost,objective,objective_overload,time.time()-t

def update_rubust_district_info(ulevel, rlevel):
	global objective_overload
	global objective
	global biobjective
	global objective_fcost
	global district_info
	global objective_supply

	for k in range(num_districts):
		district_info[k][0] = 0
		district_info[k][1] = 0.0
		district_info[k][2] = 0.0
		district_info[k][3] = 0.0
		district_info[k][4] = 0.0
	for k in range(num_districts):
		if centersID[k]<0 and k in node_groups:
			arcpy_print("debug: a facility not selected but used: " + str(k))
			#centersID[k]=facilityCandidate[k]
	for k in range(num_districts):
		if centersID[k]<0:
			continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		district_info[k][0] = len(ulist)
		district_info[k][1] = sum(nodes[x][3] for x in ulist)
		district_info[k][2] = sum(nodedik[x][k] for x in ulist)
		district_info[k][3] = facilityCapacity[k] 
		#∑i∈Idˉixij+zjΓj+∑i∈Ipij+wi≤qjyj,∀j∈J
		district_info[k][4] = robust_overload(k,ulevel, rlevel)
		#print centersID,node_groups
	bal=sum(x[4] for x in district_info)
	objective=sum([x[2] for x in district_info])
	objective_overload=bal

	biobjective=objective+objective_overload*penalty_on_demand
	objective_supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x] >=0)
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x] >=0)
	objective_fcost=fcost
	if fixed_cost_obj==1:
		biobjective+=fcost
	if max_facility_cost>0:        
		biobjective += penalty_on_demand*max(0,fcost-max_facility_cost)

def robust_overload(k,ulevel, rlevel):
	#z+p_j>=dw_j
	#∑wj+zΓ+∑pj+w ≤q
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	prob = pulp.LpProblem("ol",pulp.LpMinimize)
	pvariables={}
	for j in ulist:
		pvariables["p_" +str(j)]=pulp.LpVariable("p_" +str(j), 0, None, pulp.LpContinuous)
	zvariables=pulp.LpVariable("z", 0, None, pulp.LpContinuous)
	xvariables=pulp.LpVariable("x", 0, None, pulp.LpContinuous)
	obj=xvariables
	prob+=obj
	for j in ulist:
		s= zvariables+pvariables["p_" +str(j)]
		prob += s >= nodes[j][3]*ulevel[j]
	s=""
	for j in ulist:
		s += pvariables["p_" +str(j)]
	s+=rlevel*zvariables - xvariables
	prob += s <=  facilityCapacity[k] - sum(nodes[x][3] for x in ulist)
	gap=0.0000000001    
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(msg=0,gapRel = gap)
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=0,options=['set mip tolerances mipgap '+ str(gap)])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(msg=0,options=[("MIPGap",gap)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	for v in prob.variables():
		if v.name=="x": 
			return v.varValue


def robust_sub_model(ulevel, rlevel, timeLimit,mipgap):
	global centersID
	global node_groups
	global time_LNS1
	t=time.time()
	dlist=[]
	ulist=[]
	neigborhood_index=0
	if len(sub_model_neigborhood_types)==1:
		neigborhood_index=sub_model_neigborhood_types[0]
	if len(sub_model_neigborhood_types)==0:
		neigborhood_index=0
	if len(sub_model_neigborhood_types)>1:       
		idx=random.randint(0,len(sub_model_neigborhood_types)-1)
		neigborhood_index=sub_model_neigborhood_types[idx]
	#0 circle, 1 corridor, 2 large circle, 3 very large
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	r=random.random()
	neig=neigborhood_index
	try_times=0
	while try_times<num_units/2:
		try_times+=1
		if neigborhood_index==0:
			dlist,clist=select_region(-1)
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
		if neigborhood_index==1:
			dlist,clist=select_corridor_region()
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
		if neigborhood_index==2:
			dlist,clist=select_region_adaptive(-1)
			ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
		if neigborhood_index==3:
			if nf<=30:
				dlist=[x for x in range(num_districts) if centersID[x]>=0]
				ulist=range(num_units)
				clist=[x for x in range(num_districts) if centersID[x]<0 and x not in exclusion]
				random.shuffle(clist)
			else:
				u=random.randint(0,num_units-1)
				dlist=[]
				u=random.randint(0,num_units-1)
				for k in NearFacilityList[u]:
					if centersID[k]>=0:
						dlist.append(k)
					if len(dlist)>=min(30,nf):
						break
				ulist=[x for x in range(num_units) if nodes[x][3]>0 and node_groups[x] in dlist]
				clist=[x for x in NearFacilityList[u] if centersID[x]<0 and x not in exclusion]
				random.shuffle(clist)
		break

	nfnu=len(dlist)*len(ulist)
	ratio=max(1.0,1.0*large_neigborhood_maxIJ/len(ulist)/len(dlist))    
	ratio=min(ratio, 0.5*len(ulist)/len(dlist)) #num of candadates < len(ulist)/2
	numcl=len(dlist)*ratio   
	clist=clist[:int(numcl)]
	centers=list(set(clist+dlist))
	exist_centers=[]#[x for x in range(num_districts) if centersID[x]>=0 and x not in dlist]
	prob = pulp.LpProblem("cflp_sub",pulp.LpMinimize)
	xvariables={}
	yvariables={}
	pvariables={}
	wvariables={}
	zvariables={}

	costs={}
	penalty=penalty_on_demand
	for i in ulist:
		for j in centers+exist_centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpBinary)
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j] 
			#pvariables["p_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("p_" +str(i)+ "_"+ str(j), 0, None, pulp.LpContinuous)

	for i in ulist:
		for j in centers:
			pvariables["p_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("p_" +str(i)+ "_"+ str(j), 0, None, pulp.LpContinuous)

	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]
		wvariables["w_" +str(i)]=pulp.LpVariable("w_" +str(i), 0, None, pulp.LpContinuous) #overload
		zvariables["z_" +str(i)]=pulp.LpVariable("z_" +str(i), 0, None, pulp.LpContinuous) #robust
	cvariable=pulp.LpVariable("c", 0, None, pulp.LpContinuous) #above max_cost

	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for x in xvariables:
		obj+=costs[x]*xvariables[x]
	for x in wvariables:
		obj += penalty*wvariables[x]
	if max_facility_cost>0:
		obj+= penalty*cvariable
	prob += obj

	for i in ulist:
		s=""
		for j in centers+exist_centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1

	for i in ulist:
		for j in centers:
			s=xvariables["x_" +str(i)+ "_"+ str(j)]-yvariables["y_" +str(j)]
		prob += s<=0

	for k in centers:
		s= wvariables["w_" +str(k)]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)]
		prob += s <= 0

	for k in centers:
		for i in ulist:
			s=zvariables["z_" +str(k)] + pvariables["p_" +str(i)+"_"+str(k)] 
			s-=nodes[i][3]*ulevel[i]*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s >= 0

	'''for k in centers:
		for i in ulist:
			s=pvariables["p_" +str(i)+"_"+str(k)] - nodes[i][3]*ulevel[i]*xvariables["x_" +str(i)+"_"+str(k)]
			prob +=s <= 0'''

	#j∈Jwjxij+Γzi+j∈Jpij≤siyi,∀i∈I#5 
	robust_level=rlevel
	for k in centers:
		s=""
		for i in ulist:
			s+= pvariables["p_" +str(i)+"_"+str(k)] + nodes[i][3]*xvariables["x_" +str(i)+"_"+str(k)]
		s+= robust_level*zvariables["z_" +str(k)] 
		s-= wvariables["w_" +str(k)]
		s-= facilityCapacity[k]*yvariables["y_" +str(k)] 
		prob +=s <= 0

	for k in exist_centers:
		ilist=[x for x in range(num_units) if node_groups[x]==k]
		supply=facilityCapacity[k]-sum(nodes[x][3]*(1+ulevel[x]) for x in ilist)
		if supply<0:supply=0
		s=""
		for i in ulist:
			s+= nodes[i][3]*(1+ulevel[i])*xvariables["x_" +str(i)+"_"+str(k)]
		prob +=s <= supply
		#print "supply:",supply,
	#i∈Ifiyi≤C#6 
	if max_facility_cost>0:
		efcost=0.0
		for k in range(num_districts):
			if centersID[k]<0: continue
			if k in centers: continue
			efcost+=facilityCost[k]
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		prob += s-cvariable <= max_facility_cost-efcost
		#prob += s <= max_facility_cost-efcost
	if adaptive_number_of_facilities==0:
		s=""
		for k in centers:
			s+=yvariables["y_" +str(k)]
		prob += s == len(dlist)
		
	initvalues=loc_sub_mst(dlist,ulist)
	for x,v in initvalues:
		if x.find("x")==0 and x in xvariables:  xvariables[x].setInitialValue(v)
		if x.find("y")==0: yvariables[x].setInitialValue(v)
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=timeLimit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message,warmStart=True, timeLimit=timeLimit,options=[("MIPGap",gap),("TimeLimit",timeLimit)])
	solver.setTmpDir()
	solver.actualSolve(prob)
	
	if prob.status<=0:
		print "model 'sscflpr_sub_model' unsolved... or infeasible, msg=", prob.status
		prob.writeLP("_sscflpr_sub_model.lp")
		return 0,dlist
	fcost1=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
	
	nlist=[]
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	old_centers = centersID[:] #[x for x in range(num_districts) if centersID[x]>=0]
	for x in dlist: centersID[x]=-1
	#for x in ulist: node_groups[x]=-1
	for v in prob.variables():
		if (v.varValue >= 0.9):
			if v.name=="c": 
				continue
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='p': continue
			if items[0]=='z': continue
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
				nlist.append(i)
			if items[0]=='x':
				#print v.name, centers
				node_groups[i]=int(items[2])
	time_LNS1+=time.time()-t
	return neigborhood_index
	
#formula (17) in Bertsimas and Sim, 2004 
#bug?
def B(n,gamma):
	if gamma<0.0000001: return 0.5
	#if n>=gamma-0.000001: return 0.000001
	v=(n+gamma)/2.0
	v2=int(v)
	mu=v-v2
	x=(1-mu)*comb(n,v2)
	for i in range(v2+1, n+1): 
		x+=comb(n,i)
		#print n,i,x
	return x/pow(2,n)
def comb(n,m):
	x=1.0
	for i in range(m+1, n+1):
		x*=i
	for i in range(1, n-m+1):
		x/=i
	return x        

#uniform distribution
def overload_possiblity(ulevel,rlevel):
	rstat=[0,0,0]
	print "-------------overload possibility----------------"
	#P(si>sigma_wj)     #CDF index 0.0~3.4
	CDF=[0.5,0.5398,0.5793,0.6179,0.6554,0.6915,0.7257,0.758,0.7881,0.8159,
			0.8413,0.8643,0.8849,0.9032,0.9192,0.9332,0.9452,0.9554,0.9641,0.9713,
			0.9772,0.9821,0.9861,0.9893,0.9918,0.9938,0.9953,0.9965,0.9974,0.9981,
			0.9987,0.999,0.9993,0.9995,0.9997]
	for k in range(num_districts):
		if district_info[k][0]==0: continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		mean=sum(nodes[x][3] for x in ulist)
		var=sum(nodes[x][3]*ulevel[x]*nodes[x][3]*ulevel[x]/3 for x in ulist)
		std=int((facilityCapacity[k]-mean)/math.sqrt(var)*10)
		p=CDF[min(std,34)]
		print "facility:",k,district_info[k], 1-CDF[min(std,34)],"<", int(B(min(200,district_info[k][0]),rlevel)*1000)/1000.0
		if p>=0.90: rstat[0]+= district_info[k][1]       
		if p>=0.95: rstat[1]+= district_info[k][1]       
		if p>=0.99: rstat[2]+= district_info[k][1]       
	print "0.90/0.95/0.99", rstat[0]*1.0/total_pop,rstat[1]*1.0/total_pop,rstat[2]*1.0/total_pop
	print "warning: the possibility by formula (17) (Bertsimas & Sim, 2004) IS NOT accurate when nj<20!!!"
	print "-------------end of overload possibility----------------"

#normal distribution
def overload_possiblity_normal(stdev,rlevel):
	print "-------------overload possibility----------------"
	#P(si>sigma_wj) 
	#CDF index 0.0~3.4
	CDF=[0.5,0.5398,0.5793,0.6179,0.6554,0.6915,0.7257,0.758,0.7881,0.8159,
			0.8413,0.8643,0.8849,0.9032,0.9192,0.9332,0.9452,0.9554,0.9641,0.9713,
			0.9772,0.9821,0.9861,0.9893,0.9918,0.9938,0.9953,0.9965,0.9974,0.9981,
			0.9987,0.999,0.9993,0.9995,0.9997]
	for k in range(num_districts):
		if district_info[k][0]==0: continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		mean=sum(nodes[x][3] for x in ulist)
		var=sum(stdev[x]*stdev[x] for x in ulist)
		std=int((facilityCapacity[k]-mean)/math.sqrt(var)*10)
		#if std>34:std=34
		#print district_info[k],std, 1-CDF[min(std,34)], int(B(min(200,district_info[k][0]),rlevel)*1000)/1000.0
		#print [[nodes[x][3],ulevel[x]] for x in ulist]
		s="facility: "+str(k)+" "+str(district_info[k])+" P(demands<=supply) > "+ str(CDF[min(std,34)])
		print s

#alpha ~ z, p(x>z)=alpha
#0.1 ~ 1.2816
#0.05 ~ 1.6449
#0.01 ~ 2.3263
#0.001 ~ 3.0902
#0.0001~ 3.7190
def alpha2z(alpha): 
	robust_level=1-alpha
	alpha_idx={0.1:1.2816,0.05:1.6449,0.01:2.3263,0.001:3.0902,0.0001:3.7190}
	if alpha in alpha_idx:
		return alpha_idx[alpha]    
	CDF=   [0.5,0.5398,0.5793,0.6179,0.6554,0.6915,0.7257,0.758,0.7881,0.8159,
			0.8413,0.8643,0.8849,0.9032,0.9192,0.9332,0.9452,0.9554,0.9641,0.9713,
			0.9772,0.9821,0.9861,0.9893,0.9918,0.9938,0.9953,0.9965,0.9974,0.9981,
			0.9987,0.999,0.9993,0.9995,0.9997]
	za=34
	for i in range(34):
		if CDF[i] >= robust_level:
			za=i
			break
	#print("alpha->za: "+str(alpha)+"->"+str(za/10.0))
	return za / 10.0

#poisson_distribution
#x~Poisson(lambda),P(x>z)<alpha
#(k-\lambda)/\sqrt[2]{\lambda}=z
def max_alpha2z(maxs,alpha):
	if maxs<50:
		return max_alpha2z_exact(maxs,alpha)
	za=alpha2z(alpha)
	x1=1.0
	x2=maxs*1.0
	while 1:
		x=(x1+x2)/2
		z=(maxs-x)/math.sqrt(x)
		if z<za:
			x2=x
		else:
			x1=x
		#print za,x1,x2
		if x2-x1<0.01: 
			break
	return x1
def max_alpha2z_exact(maxs,alpha):
	x1=1.0
	x2=maxs*1.0
	while 1:
		x=(x1+x2)/2
		p=math.exp(-x) #k=0
		for k in range(1,int(maxs)+1):
			pk=math.exp(-x)*math.pow(x,k)
			for i in range(1,k+1):
				pk /= i
			p+=pk        
			#print x,pk,p
		if 1-p<alpha:
			x1=x
		else:
			x2=x
		#print x1,x2,p
		if x2-x1<0.001: 
			break
	#print x1
	return x1    
	
		
def test_reliable_facility():
	supply=[random.randint(100,200) for x in range(10)]
	frate=[random.randint(5,20)/100.0 for x in range(10)]
	z=2.5
	a=sum(supply)
	b=0.0
	for i in range(10):
		b+=(1-frate[i])*frate[i]*supply[i]*supply[i]
	b=(1-frate[i])*a+z*pow(b,0.5)
	print a,b
	print supply
	print frate