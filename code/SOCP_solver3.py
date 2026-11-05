import sys,os,random,time,copy,math,tempfile#, keyboard
import gurobipy as gp
from gurobipy import GRB
#constant
MAXNUMBER=1.0e+20
MINNUMBER=1.0e-20
bigM=10000.0

#instance info
nodes=[]
nodes_std=[] #for homoDP only
demand_sigma=[]
weight_features=[] #for homoDP only
num_units=-1
nodedij=[]
nodedik=[]	#weighted cost from i to k, =nodedij*nodes[][3] 
nodendij=[] #network distance
node_neighbors=[]
facility_neighbors=[]
total_pop=0
avg_pop=0
total_supply=0
distance_type=0 #0 Euclidean, 1 Manhattan, 2 Geo, 3 Network
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
#for HEMS
fnodes=[]
nodecij=[]
facilityBaseCost=2.0
facility_max_helicopters=3
helicopter_fixed_Cost=1.5
helicopter_flight_fixed_cost=0.5
helicopter_flight_hour_cost=1.0
helicopter_speed_hour=200
helicopter_service_capacity=4

#problem parameters
location_problem=1 #11 location and size
reliable_level=0.5
za_reliable=10.0
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

stop_searching=0
'''def on_key_event(e):
	global stop_searching
	#print e.name    
	if e.name=="esc":
		stop_searching=1    
		print("\nuser break...!")
keyboard.on_press_key('esc', on_key_event)'''
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
			print("debug: a facility not selected but used: " + str(k))
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
	biobjective=objective+objective_overload*penalty_on_demand
	objective_supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x] >=0)
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x] >=0)
	objective_fcost=fcost
	if fixed_cost_obj==1:
		biobjective+=fcost
	move_count+=1

def update_envy_district_info():
	global biobjective
	global objective_envy
	envyobj=0.0
	for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
	objective_envy=envyobj
	biobjective = objective*(1-envy_objective_weight) + envyobj *envy_objective_weight
	biobjective += objective_overload*penalty_on_demand 
	if fixed_cost_obj==1:
		biobjective+=objective_fcost
	if fixed_cost_obj==0 and max_facility_cost>0:
		biobjective += penalty_on_demand*max(0,objective_fcost-max_facility_cost)

def sol_stat():
	fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)    
	fcapa=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)    
	print( [x for x in range(num_districts) if centersID[x]>=0])   
	print("fc,fcapa:",fc,fcapa)
	print( [facilityCost[x] for x in range(num_districts) if centersID[x]>=0])   
	print( [facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0])

	fcost=objective_fcost
	sol={}
	sol["num_facility"]=sum(1 for x in centersID if x>=0)
	if len(fnodes)>0:
		hn=0
		for k in range(num_districts):
			if centersID[k]<0: continue
			n= int(facilityCapacity[k]/helicopter_service_capacity+0.1)
			hn+=n
		sol["num_helicopter"]=hn
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

def print_equality_measures():
	#print "-----------equality measures---------------"
	#update_district_info()
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
def readUncertainFlpFile(f1,f2):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global fnodes
	global node_neighbors
	global nodedij
	global nodecij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global potential_facilities
	global facilityBaseCost
	global facility_max_helicopters
	global helicopter_fixed_Cost
	global helicopter_flight_fixed_cost
	global helicopter_flight_hour_cost
	global helicopter_speed_hour
	global helicopter_service_capacity
	
	node =[0,0,0,0,0,0,0,0,0,0]
	nodes = []
	f = open(f1)
	line = f.readline()  #num_units, num_scenarios,   res,res,res, Mean_5,Stdev_6, demand_7....7+num_scenarios
	items = line.split()
	num_units=int(items[0])
	num_scenarios=int(items[1])
	Kset=[[0 for x in range(num_units)] for y in range(num_scenarios)]
	Kp=[1 for y in range(num_scenarios)]
	#print num_scenarios, items   
	for k in range(num_scenarios):
		Kp[k]=int(items[k+7])
	line = f.readline()
	nodeidx=0
	while nodeidx<num_units:
		line = f.readline()
		items = line.split()
		#print line, #items
		unit=[int(items[0]), float(items[1]), float(items[2]), float(items[5]),float(items[6]),-1]
		nodes.append(unit)
		for k in range(num_scenarios):  
			Kset[k][nodeidx]=float(items[k+7])
		nodeidx+=1
		#line = f.readline()
	f.close()
	total_pop=sum(x[3] for x in nodes)
	f = open(f2)
	line = f.readline()
	items = line.split()
	HcostFixed=float(items[1])
	line = f.readline()
	items = line.split()
	HServeFixCost=float(items[1])
	line = f.readline()
	items = line.split()
	HFlightHourCost=float(items[1])
	line = f.readline()
	items = line.split()
	HSpeed=float(items[1])
	line = f.readline()
	items = line.split()
	helicopter_service_capacity=float(items[1])

	helicopter_fixed_Cost=HcostFixed
	helicopter_flight_fixed_cost=HServeFixCost
	helicopter_flight_hour_cost=HFlightHourCost
	helicopter_speed_hour=HSpeed
	print ("helicopter_fixed_Cost"+str(HcostFixed))
	print ("helicopter_flight_fixed_cost"+str(HServeFixCost))
	print ("helicopter_flight_hour_cost"+str(HFlightHourCost))
	print ("helicopter_speed_hour"+str(HSpeed))
	print ("helicopter_service_capacity"+str(helicopter_service_capacity))
	line = f.readline()
	line = f.readline()
	nodeidx=0
	fnodes=[]
	while line:
		items = line.split()
		unit=[int(items[0]), float(items[1]), float(items[2]), float(items[3]),float(items[4]),float(items[5]),float(items[6]),0]
		fnodes.append(unit)
		#print unit
		nodeidx+=1
		line = f.readline()
	f.close()
				
	num_districts=len(fnodes)
	
	facilityCandidate=[x[0] for x in fnodes]
	centersID=facilityCandidate[:]
	facilityCost=[x[3] for x in fnodes]
	facilityCapacity=[x[4] for x in fnodes]
	facilityBaseCost=[x[5] for x in fnodes]
	facility_max_helicopters=[x[6] for x in fnodes]

	total_supply=sum(facilityCapacity)
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]

	for i in range(num_units):
			for k in range(num_districts):
				d=0.0
				d2=pow(nodes[i][1]-fnodes[k][1],2)
				d2+=pow(nodes[i][2]-fnodes[k][2],2)
				d=pow(d2,0.5)/1000
				nodedij[i][k]=HServeFixCost+d/HSpeed*HFlightHourCost  #for helicopter only: cost=hop(0.5)+dij/speed*rate
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print ("find_near_customer()...")
	find_near_customer()
	#create_node_neighbors()
	#find_nearFacilityFacility()
	print ("create_facility_neighbors()...")
	#create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="M N: "+str(num_districts)+" "+str(num_units)
	print(s)
	#print nodedij
	#s="Demand and supply: "+str(total_pop)+" "+str(sum(facilityCapacity))
	#print(s)    
	tw=1.0*sum(Kp)
	Kps=[x/tw for x in Kp]
	return num_scenarios,Kset,Kps,fnodes

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
	print ("reading nodes ...")
	f = open(f1)
	line = f.readline()	 #OID	 pop	PointX	  PointY	fcadidature	   fcost	fcapacity
	line = f.readline()
	nodeidx=0
	while line:
		items = line.split()
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
	print ("all data are read! ")
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

	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	max_dij=0.0
	print ("craeating distance matrix......")
	for i in range(num_units):
		for k in range(num_districts):
			j=facilityCandidate[k]
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
	print ("find_near_customer()...")
	find_near_customer()
	#find_nearFacilityFacility()
	print ("create_facility_neighbors()...")
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="M N: "+str(num_districts)+" "+str(num_units)
	print(s)
	s="Total demand & supply: "+str(total_pop)+" "+str(total_supply)+" "+str(sum(facilityCost))
	print(s)

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
	line = f.readline()	 #OID	 pop	PointX	  PointY	fcadidature	   fcost	fcapacity
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
	print ("find_near_customer()...")
	find_near_customer()
	#find_nearFacilityFacility()
	print ("create_facility_neighbors()...")
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]

	node_neighbors = [[]for x in range(len(nodes))]
	s="M N: "+str(num_districts)+" "+str(num_units)
	s+="\nTotal demand: "+str(total_pop)
	s+="\nTotal supply: "+str(total_supply)
	s+="\nTotal cost: "+str(sum(facilityCost))
	print(s)

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
	print("M,N: "+str(num_districts)+" "+str(num_units))
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
				i=int ((idx-num_units)%num_units)
				k=int ((idx-num_units)/num_units)
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
	print(s)
	s="total supply: "+str(total_supply)
	print(s)

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
	print("M,N: "+str(num_districts)+" "+str(num_units))

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
			k=int(idx/num_units)
			i=int(idx%num_units)
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
	print(s)
	s="total supply: "+str(total_supply)
	print(s)

def find_NearFacilityList(nnn):
	global NearFacilityList
	if len(NearFacilityList)>0: return
	NearFacilityList=[]
	n=nnn#num_districts
	if n>num_districts: n=num_districts
	dis=0.0
	print( "find_NearFacilityList()...")
	for i in range(num_units):
		fdlist=[ [x,nodedij[i][x]] for x in range(num_districts)]
		fdlist.sort(key=lambda x:x[1])
		flist=[x[0] for x in fdlist[0:n]]
		NearFacilityList.append(flist[:])
	print ("data samples:")
		
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

#Chance constraint CFLP 
#SOCP solved by Gurobi
#from gurobipy import Model, GRB
def CFLP_SOCP_mip(sigma,rlevel,time_limit,mipgap): 
	global centersID
	global node_groups

	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	m =gp.Model("_CC_CFLP")
	y = m.addVars(centers, vtype=GRB.BINARY, name="y") 
	x = m.addVars(ulist, centers, vtype=GRB.BINARY, name="x") 
	z = m.addVars(centers,lb=0.0, name="z")

	if envy_service_objective==0:
		if fixed_cost_obj==0:
			m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)+ sum(penalty_on_demand*z[k] for k in centers), GRB.MINIMIZE)
		if fixed_cost_obj==1:
			m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)+sum(facilityCost[k]*y[k] for k in centers)+ sum(penalty_on_demand*z[k] for k in centers) , GRB.MINIMIZE)
	if envy_service_objective==1:
		c=[ [0.0 for j in centers] for i in ulist]
		for i in ulist:
			for j in centers:
				d=max(0, nodedij[i][j]-envy_service_distance)
				c[i][j]=travel_distance_weight*nodedik[i][j] + envy_objective_weight*nodes[i][3]*d*d
		m.setObjective(sum(c[i][j] * x[i,j] for i in ulist for j in centers) + sum(penalty_on_demand*z[k] for k in centers) + penalty_on_demand*w, GRB.MINIMIZE)	

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")

	for i in ulist:
		for j in centers:
			m.addConstr(x[i,j] <= y[j], name=f"assign_{i}_{j}")

	for i in ulist:
		for j in centers:
			if nodedij[i][j]<=cflp_max_service_radius: continue
			m.addConstr(x[i,j] == 0, name=f"assign_zero_{i}_{j}")
            
	cover_expr=gp.LinExpr()
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>cflp_service_radius_preference: continue
			cover_expr+=nodes[i][3]*x[i,j]
	m.addConstr(cover_expr >= total_pop/100.0*cflp_min_service_coverage_percentage, name=f"min_cover")

	if adaptive_number_of_facilities==0:
		m.addConstr(y.sum() == max_num_facility, "open_p")


	za=alpha2z(rlevel)
	print("chance: "+str(rlevel)+" -> za: "+str(za))
	demands=[nodes[i][3] for i in ulist]
	for j in centers:
		s = m.addVar(lb=0.0, name=f"s_{j}")
		quad_expr=gp.QuadExpr()
		for i in ulist:
			quad_expr+=sigma[i]*sigma[i]*x[i,j]
		m.addQConstr(quad_expr <= s*s, name=f"soc_{j}")
		m.addConstr(sum(demands[i] * x[i,j] for i in ulist) + za * s <=z[j]+ facilityCapacity[j] * y[j], name=f"chance_{j}")
		m.addConstr( z[j]<= bigM*y[j], name=f"ol_{j}")

	'''ratio=sum(facilityCapacity)/total_pop
	for i in ulist:
		klist=[k for k in NearFacilityList[i] if k in centers]
		for k in klist[int(ratio*10):]:
			if len(node_groups)>0 and node_groups[i]==k: continue #for warm start only
			m.addConstr(x[i,k] == 0, name=f"assign0_{i}_{k}")'''

	if len(node_groups)>0:
		for k in centers:
			if centersID[k]>=0:
				y[k].start=1.0
		for i in ulist:
			k=node_groups[i]
			x[i,k].start=1.0

	m.write("_cccflp.lp")
	m.Params.OutputFlag = solver_message
	m.Params.TimeLimit = time_limit
	m.Params.MIPGap = mipgap
	#m.Params.MIPFocus=0
	#m.Params.NoRelHeurSolutions=5
	m.Params.Heuristics=0.5
	m.optimize()

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]

	for i in ulist:
		for j in centers:
			if x[i,j].X > 0.5:
				node_groups[i]=j
	for j in centers:
		if y[j].X > 0.5:
			centersID[j]=facilityCandidate[j]
	update_district_info()
	return 1  

def CFLSP_SOCP_mip(sigma,rlevel,time_limit,mipgap): 
	global centersID
	global node_groups

	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	m =gp.Model("CC_CFLP")
	y = m.addVars(centers, vtype=GRB.BINARY, name="y") 
	x = m.addVars(ulist, centers, vtype=GRB.BINARY, name="x") 
	z = m.addVars(centers,lb=0,  vtype=GRB.INTEGER,name="z")

	w=m.addVar(lb=0.0, name="m")

	m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)+sum(fnodes[k][5]*y[k] for k in centers)+ sum(helicopter_fixed_Cost*z[k] for k in centers) , GRB.MINIMIZE)

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")
	for i in ulist:
		for j in centers:
			m.addConstr(x[i,j] <= y[j], name=f"assign_{i}_{j}")

	for i in ulist:
		for j in centers:
			if nodedij[i][j]<=cflp_max_service_radius: continue
			m.addConstr(x[i,j] == 0, name=f"assign_zero_{i}_{j}")
            
	cover_expr=gp.LinExpr()
	for i in ulist:
		for j in centers:
			if nodedij[i][j]>cflp_service_radius_preference: continue
			cover_expr+=nodes[i][3]*x[i,j]
	m.addConstr(cover_expr >= total_pop/100.0*cflp_min_service_coverage_percentage, name=f"min_cover")

	if adaptive_number_of_facilities==0:
		m.addConstr(y.sum() == max_num_facility, "open_p")
	for j in centers:
		m.addConstr(z[j]<=fnodes[j][6]*y[j],name=f"ub_{j}")

	za=alpha2z(rlevel)
	print("chance: "+str(rlevel)+" -> za: "+str(za))
	demands=[nodes[i][3] for i in ulist]
	for j in centers:
		s = m.addVar(lb=0.0, name=f"s_{j}")
		quad_expr=gp.QuadExpr()
		for i in ulist:
			quad_expr+=sigma[i]*sigma[i]*x[i,j]
		m.addQConstr(quad_expr <= s*s, name=f"soc_{j}")
		m.addConstr(sum(demands[i] * x[i,j] for i in ulist) + za * s <= helicopter_service_capacity * z[j], name=f"chance_{j}")


	if len(node_groups)>0:
		for k in centers:
			if centersID[k]>=0:
				y[k].start=1.0
		for i in ulist:
			k=node_groups[i]
			x[i,k].start=1.0

	m.write("_cccflp.lp")
	m.Params.OutputFlag = solver_message
	m.Params.TimeLimit = time_limit
	m.Params.MIPGap = mipgap
	#m.Params.MIPFocus=0
	#m.Params.NoRelHeurSolutions=5
	m.Params.Heuristics=0.5
	m.optimize()

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]

	for i in ulist:
		for j in centers:
			if x[i,j].X > 0.5:
				node_groups[i]=j
	for j in centers:
		if y[j].X > 0.5:
			centersID[j]=facilityCandidate[j]
		if z[j].X > 0.5:
			nh=int(z[j].X+0.001)
			fnodes[j][3]=fnodes[j][5]+nh*helicopter_fixed_Cost
			fnodes[j][4]= nh*helicopter_service_capacity
			facilityCost[j]=fnodes[j][5]+nh*helicopter_fixed_Cost
			facilityCapacity[j]= nh*helicopter_service_capacity
	update_district_info()
	return 1  



#testing
def CFLP_relax_mip(time_limit,mipgap): 
	global centersID
	global node_groups
	centers=[x for x in range(num_districts)]#facilityCandidate
	ulist=range(num_units)
	acap=sum(facilityCapacity)/num_districts
	nf=int(5*total_pop/acap+0.99)
	random.shuffle(centers)
	centers=centers[:nf]

	m =gp.Model("CC_CFLP")
	y = m.addVars(centers, vtype=GRB.BINARY, name="y") 
	x = m.addVars(ulist, centers, lb=0.0, ub=1.0, name="x") 

	if fixed_cost_obj==0:
			m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers), GRB.MINIMIZE)
	if fixed_cost_obj==1:
			m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)+sum(facilityCost[k]*y[k] for k in centers), GRB.MINIMIZE)

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")

	for i in ulist:
		for j in centers:
			m.addConstr(x[i,j] <= y[j], name=f"assign_{i}_{j}")

	if adaptive_number_of_facilities==0:
		m.addConstr(y.sum() == max_num_facility, "open_p")

	if max_facility_cost>0:
		m.addConstr(sum(facilityCost[k]*y[k] for k in centers) <= max_facility_cost, "open_cost")

	demands=[nodes[i][3] for i in ulist]
	for j in centers:
		m.addConstr(sum(demands[i] * x[i,j] for i in ulist) <= facilityCapacity[j] * y[j], name=f"chance_{j}")

	'''ratio=sum(facilityCapacity)/total_pop
	for i in ulist:
		klist=[k for k in NearFacilityList[i] if k in centers]
		for k in klist[int(ratio*6):]:
			m.addConstr(x[i,k] == 0, name=f"assign0_{i}_{k}")'''

	m.Params.OutputFlag = solver_message
	m.Params.TimeLimit = time_limit
	m.Params.MIPGap = mipgap
	m.Params.MIPFocus=0
	m.Params.Heuristics=0.5
	m.optimize()

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	ilist=[0.0 for i in range(num_units)]
	for i in ulist:
		for j in centers:
			if x[i,j].X > ilist[i]:
				node_groups[i]=j
				ilist[i]=x[i,j].X
	for j in centers:
		if y[j].X > 0.5:
			centersID[j]=facilityCandidate[j]
	update_rubust_district_info(demand_sigma,za_reliable)
	return 1  

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
	
def CEECFLP_SOCP_MH(sigma, rlevel,psize,maxloops):
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
	print	("----------------original problem definition------------------")
	print	("envy_service_objective: "+str(envy_service_objective))
	print	("envy_service_distance: "+str(envy_service_distance))
	print	("envy_objective_weight: "+str(envy_objective_weight))
	print	("travel_distance_weight: "+str(travel_distance_weight))
	print ("Solving by distance equivilent problems... ")
	nodedij_org=copy.deepcopy(nodedij)
	nodedik_org=copy.deepcopy(nodedik)
	for i in range(num_units):
		for j in range(num_districts):
				d=nodedij[i][j]
				nodedij[i][j]=d*travel_distance_weight
				d2=max(0,d-envy_service_distance)
				nodedij[i][j]+=envy_objective_weight*d2*d2
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]
	#cflp_max_service_radius=envy_service_distance*travel_distance_weight+envy_objective_weight*9*envy_service_distance*envy_service_distance
	envy_service_objective_back=envy_service_objective
	envy_objective_weight_back=envy_objective_weight
	travel_distance_weight_back=travel_distance_weight
	envy_service_objective=0
	envy_objective_weight=0        
	travel_distance_weight=1

	print	("----------------equivilent problem definition------------------")
	print	("envy_service_objective: "+str(envy_service_objective))
	#print	("envy_service_distance: "+str(envy_service_distance))
	print	("envy_objective_weight: "+str(envy_objective_weight))
	print	("travel_distance_weight: "+str(travel_distance_weight))
	print	("large_neigborhood_maxIJ: "+str(large_neigborhood_maxIJ))
	if initial_solution_method==9:
		CFLP_SOCP_mip(sigma,rlevel,7200,0.001)		
	pop=CC_CFLP_matheuristic(sigma, rlevel,psize,maxloops)
	nodedij=nodedij_org
	nodedik=nodedik_org
	node_groups=best_solution_global
	centersID=best_centersID_global
	envy_service_objective=envy_service_objective_back
	envy_objective_weight=envy_objective_weight_back
	travel_distance_weight=travel_distance_weight_back
	za=alpha2z(rlevel) 
	update_rubust_district_info(sigma, za)
	return pop
    
def DCCFLP_SOCP_MH(sigma, rlevel,psize,maxloops):
	global nodedij
	global nodedik
	global node_groups
	global centersID
	global solver_message
	global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	initialize_instance()    
	print	("----------------original problem definition------------------")
	print	("cflp_max_service_radius: ",cflp_max_service_radius)
	print	("cflp_service_radius_preference: ",cflp_service_radius_preference)
	print	("cflp_min_service_coverage_percentage: ",cflp_min_service_coverage_percentage)
	print	("penalty_on_demand: ",penalty_on_demand)

	print ("Solving by distance equivilent problems... ")
	nodedij_org=copy.deepcopy(nodedij)
	nodedik_org=copy.deepcopy(nodedik)
	for i in range(num_units):
		for j in range(num_districts):
				d=nodedij[i][j]
				d2=d+max(0,d-cflp_max_service_radius)*penalty_on_demand
				nodedij[i][j]=d2
				nodedik[i][j]=nodes[i][3]*nodedij[i][j]

	if initial_solution_method==9:
		CFLP_SOCP_mip(sigma,rlevel,7200,0.001)		
	pop=CC_CFLP_matheuristic(sigma, rlevel,psize,maxloops)
	nodedij=nodedij_org
	nodedik=nodedik_org
	#node_groups=best_solution_global
	#centersID=best_centersID_global
	za=alpha2z(rlevel) 
	update_rubust_district_info(sigma, za)
	return pop

def drop_method_cflpr():
	global node_groups
	global centersID
	global all_solutions
	sol=[]
	node_groups=[NearFacilityList[x][0] for x in range(num_units)]
	centersID=facilityCandidate[:]
	#for x in range(num_districts):
	#	 if x not in node_groups: centersID[x]=-1
	if total_supply>10*total_pop:
		centersID=[-1 for x in range(num_districts)]
		sampling=1
		min_nf=int(total_pop*num_districts/total_supply)
		clist=list(range(num_districts))
		random.shuffle(clist)
		clist=clist[:min_nf*10]
		centers=list(set(clist+facility_inclusion_list))
		for k in centers: centersID[k]=facilityCandidate[k]
	for i in range(num_units):
		for k in NearFacilityList[i]:
			if centersID[k]==-1: continue
			node_groups[i]=k
			break 
	update_district_info()
	while 1:
		sol=[centersID[:],node_groups[:]]
		sta=location_drop_cflpr()	 #too slow for large instances, sampling ?
		update_district_info()
		if sta<=0: break
		sol=[biobjective,centersID[:],node_groups[:]]
		nf=sum(1 for x in centersID if x>=0)
		if adaptive_number_of_facilities==0 and nf <= max_num_facility: 
			break
		if adaptive_number_of_facilities==1 and max_facility_cost>0:
			fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
			#print ([fc,max_facility_cost])
			if fc<= max_facility_cost:           
				break
			
	#if len(sol)>0:
	#	 node_groups=sol[2][:]
	#	 centersID=sol[1][:]
	#	 update_cflpr_district_info()
	nf=sum(1 for x in centersID if x>=0)
	if adaptive_number_of_facilities==0 and nf > max_num_facility:
		droplist=[]
		dlist=[x for x in range(num_districts) if centersID[x] >=0]
		while len(dlist) >max_num_facility:
			random.shuffle(dlist)
			k=dlist[0]
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
		update_district_info()
		coverdemand=0
		for i in range(num_units):
			k=node_groups[i]
	return 1

def location_drop_cflpr(): 
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
			update_district_info()
			return status
		update_district_info()
		#print objective,objective_fcost,objective_overload
		status=1
		f_del+=1
		if f_del>=len(clist)/20 or f_del>=10: break
		supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)
		if supply<=total_pop*3: break
		nf=sum(1 for x in centersID if x>=0)
		if adaptive_number_of_facilities==0 and nf==max_num_facility:
			break
	return status

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
	#	 ##noprint "check_solution_continuality_feasibility!!!"
	#	 return improve
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

def CC_CFLP_matheuristic(sigma, rlevel, psize,maxloops):
	global best_biobjective_global
	global node_groups
	global centersID
	global facilityCost
	global facilityCapacity
	global district_info
	global region_pool
	global pool_index
	global all_solutions
	global demand_sigma
	global reliable_level
	global za_reliable
	global max_loops_solution_not_improved
	'''global cflp_max_service_radius
	global cflp_service_radius_preference
	global cflp_min_service_coverage_percentage
	global travel_distance_weight'''
	#print ("sigma, rlevel, psize, maxloops:"+str([sigma, rlevel, psize,maxloops]))
	max_loops_solution_not_improved=maxloops
	demand_sigma=sigma
	za=alpha2z(rlevel) 
	reliable_level=rlevel
	za_reliable=za

	all_solutions=[]
	region_pool=[]
	t=time.time()
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[[] for x in range(num_districts)]
	not_improved_global=0

	for idx in range(psize):
		init_t=time.time()
		#sta=drop_method_cflpr()
		CFLP_relax_mip(heuristic_time_limit/10.0,0.1)
		update_rubust_district_info(sigma, za)  
		sta=1
		#print ([0,biobjective,objective,objective_fcost,objective_overload])
		obj_old=biobjective
		while sta>0:
			sta=one_unit_move(sigma, za)        
			#print ([sta,biobjective,objective,objective_fcost,objective_overload])
		'''if objective_overload>0:
			SOCP_assign_sub_model(sigma, rlevel, 10, 0.1)'''	
		'''ol=objective_overload        
		while objective_overload>0:
			SOCP_assign_sub_model(sigma, rlevel, 20, 0.1)
			update_rubust_district_info(sigma, za)
			print([ol,objective_overload])
			if objective_overload >= ol: break
			ol=objective_overload        '''
		nf=sum(1 for x in centersID if x>=0)
		update_rubust_district_info(sigma, za)  
		population.append([biobjective,centersID[:],node_groups[:],facilityCost[:], facilityCapacity[:],objective,objective_fcost,objective_overload,0])
		s="init solution:"+str(idx) +" "+str(nf) +" "+str(int(biobjective))+" " +str(int(objective))+" "
		s+=str(int(objective_fcost))+" "+str(int(objective_overload))+" "+str(int(time.time()-t)) + " "+str(int(biobjective-obj_old))
		print(s)
     
	population.sort(key=lambda x:x[0])
	all_solutions=copy.deepcopy(population)
	loop=-1
	gap=1.0e-10
	while 1:
		r=random.random()
		sidx = int(min(psize,len(population))*pow(r,1.5))
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		facilityCost=population[sidx][3][:]
		facilityCapacity=population[sidx][4][:]    
        
		update_rubust_district_info(sigma, za)
		bnf=sum(1 for x in centersID if x>=0)
		fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		orgs=str(bnf) +" "+ str(int(biobjective))+" " +str(int(objective))+" "+str(int(fc))+" "+str(int(objective_overload))+" -> "
		obj_old=biobjective
		loop+=1
		not_improved_global+=1
		obj=best_biobjective_global
		#if not_improved_global <= max_loops_solution_not_improved/5: gap=0.1
		sta=SOCP_location_sub_model(sigma, rlevel, max(50,large_neigborhood_maxIJ/50), gap)
		#SOCP_assign_sub_model(sigma, rlevel, 50, 0.01)
		update_rubust_district_info(sigma, za)
		update_best_solution()
		population.append([biobjective,centersID[:],node_groups[:],facilityCost[:], facilityCapacity[:],objective,objective_fcost,objective_overload,0])
		#obj_old=biobjective

		#search_sta=1
		#while search_sta>0:
		#	search_sta=one_unit_move(sigma, za)  
		#update_rubust_district_info(sigma, za)
		#update_best_solution()
		#population.append([biobjective,centersID[:],node_groups[:],facilityCost[:], facilityCapacity[:],objective,objective_fcost,objective_overload,0])
		
		population.sort(key=lambda x:x[0])
		#population=pop_selection(population)
		#all_solutions=copy.deepcopy(population)
		s="" 
		if best_biobjective_global<obj-0.000001: 
			s+="*"
			impp=(best_biobjective_global-obj)/best_biobjective_global*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
		else: 
			s+="-"
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Loop "+str(loop) + str([sidx,sta])+" Best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))+" "+str(int(best_overload_global))
		bnf=sum(1 for x in centersID if x>=0)
		fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		s+=" Current: "+ orgs + str(bnf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(fc)+" "+str(int(objective_overload))
		s+=" Info: " +str(len(population))+" " + str(not_improved_global)+ " "+str(int(time.time()-t)) + " "+str(int(biobjective-obj_old))

		print(s)
		#print not_improved_global, max_loops_solution_not_improved
		if not_improved_global >= max_loops_solution_not_improved: break
		if stop_searching==1: break
		if time.time()-t>heuristic_time_limit: break

	'''print( "population:")
	for idx in range(min(3,len(population))):
		node_groups=population[idx][2]
		centersID=population[idx][1][:]
		facilityCost=population[idx][3]
		facilityCapacity=population[idx][4]   
		update_rubust_district_info(sigma, za)
		fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)    
		fcapa=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)    
		print(idx,"fc,fcapa:",fc,fcapa,population[idx][0])
		print( [x for x in range(num_districts) if centersID[x]>=0])   
		print( [facilityCost[x] for x in range(num_districts) if centersID[x]>=0])   
		print( [facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0]) 
	print( "end population")'''

	node_groups=population[0][2][:]
	centersID=population[0][1][:]
	facilityCost=population[0][3][:]
	facilityCapacity=population[0][4][:]    
	update_rubust_district_info(sigma, za)
	'''nf=sum(1 for x in centersID if x>=0)
	fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)    
	fcapa=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)    
	print("fc,fcapa:",fc,fcapa)
	print( [facilityCost[x] for x in range(num_districts) if centersID[x]>=0])   
	print( [facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0]) '''
	return population


#overload(k,sigma,za,ulist):
def one_unit_move(sigma,za): #FA
	global node_groups
	global time_op
	global count_op
	t=time.time()
	ulist=range(num_units)#find_edge_units()
	difflist=[]
	for x in ulist:
		rlist=[r for r in NearFacilityList[x] if centersID[r]>=0]
		k=node_groups[x]
		difflist.append([x,nodedik[x][rlist[0]]-nodedik[x][k]])
	difflist.sort(key=lambda x:x[1])
	ulist=[x[0] for x in difflist]
	find_best_solution=0
	for nid in ulist:
		rid=node_groups[nid]
		klist=[x for x in NearFacilityList[nid] if centersID[x]>=0 and x!=k]
		klist=klist[:8]
		for k in klist:
			if district_info[k][4]>0: continue
			savings=nodedik[nid][rid]-nodedik[nid][k]
			overload_old=district_info[rid][4] + district_info[k][4]
			kulist=[i for i in range(num_units) if node_groups[i]==rid and i!=nid]
			overload_new=reliable_overload2(rid,sigma,za,kulist) 
			kulist=[i for i in range(num_units) if node_groups[i]==k]+[nid]
			overload_new+=reliable_overload2(k,sigma,za,kulist)
			savings+= (overload_old-overload_new)*penalty_on_demand
			#print(savings)
			if savings<0.0001: continue
			node_groups[nid]=k
			count_op[0]+=1
			#print "OUM",savings,biobjective,objective,objective_overload,
			update_rubust_district_info(sigma, za)
			#print "->",biobjective,objective,objective_overload
			find_best_solution += 1#update_best_solution()
			break
	time_op[0]+=time.time()-t
	return find_best_solution

#return a list of boundary units
def find_edge_units():
	ulist=[]
	for x in range(num_units):
		k=node_groups[x]
		for y in node_neighbors[x]:
			if node_groups[y] != k:
				ulist.append(x)
				break
	random.shuffle(ulist)
	return ulist
    
def update_rubust_district_info(sigma, za):
	global objective_overload
	global objective
	global biobjective
	global objective_fcost
	global district_info
	global objective_supply
	global facilityCost
	global facilityCapacity
	'''if location_problem==11:
		facilityCost=[x[3] for x in fnodes]
		facilityCapacity=[x[4] for x in fnodes]'''
	for k in range(num_districts):
		district_info[k][0] = 0
		district_info[k][1] = 0.0
		district_info[k][2] = 0.0
		district_info[k][3] = 0.0
		district_info[k][4] = 0.0
	for k in range(num_districts):
		if centersID[k]<0 and k in node_groups:
			print("debug: a facility not selected but used: " + str(k))
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
		district_info[k][4] = reliable_overload(k,sigma, za)
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
	if envy_service_objective==1:
		update_envy_district_info()
	if cflp_service_radius_preference>0:
		covered=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]>cflp_service_radius_preference: continue
			covered+=nodes[i][3]
		covered2= max(0,total_pop/100.0*cflp_min_service_coverage_percentage-covered)
		biobjective += penalty_on_demand*covered2


def reliable_overload(k,sigma, za):
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	demand=sum(nodes[x][3] for x in ulist)
	var=sum(sigma[x]*sigma[x] for x in ulist)
	demand += za*math.sqrt(var)
	return max(0, demand-facilityCapacity[k])

def reliable_overload2(k,sigma,za,ulist):
	demand=sum(nodes[x][3] for x in ulist)
	var=sum(sigma[x]*sigma[x] for x in ulist)
	demand += za*math.sqrt(var)
	return max(0, demand-facilityCapacity[k])

def select_region(seed):
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	n=nf
	if nf<=7: 
		n=nf
	if nf>=8 and nf<=11: 
		n=random.randint(int(nf/2+1),8)
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
		d=sum(nodedik[x][k] for x in ulist)
		cflist.append([k,d])
	cflist.sort(key=lambda x: x[1])
	clist=[x[0] for x in cflist]
	clist=clist[:int(n*num_districts/nf-n)]
	clist+=[NearFacilityList[x][0] for x in ulist ]
	clist=list(set(clist))
	clist=[x for x in clist if centersID[x]<0]
	random.shuffle(clist)
	return dlist, clist

def select_corridor_region():
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	n=100*nf/num_units	#areas with 100 units
	if nf<=12: 
		return [x for x in range(num_districts) if centersID[x]>=0],[x for x in range(num_districts) if centersID[x]<0]
	if nf>=12 and nf<=16: 
		n=random.randint(7,10)
	if nf>=17: 
		n=random.randint(8,11)
	#if n*num_units/nf<80: 
	#	 n=min(10,80*nf/num_units)
	k_dis=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
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
	clist=[x for x in clist if centersID[x]<0]
	random.shuffle(clist)
	return dlist,clist

def select_region_adaptive(seed):
	nf=sum(1 for x in range(num_districts) if centersID[x]>=0)
	units=num_units/nf
	n=-1
	if units >= 50:
		if nf<=10: n=random.randint(int(nf/2+1),nf)
		if nf>=11 and nf<=20: n=random.randint(8,11)
		if nf>=21: n=random.randint(10,13)
	if units>=25 and units<=49:
		if nf<=10: n=random.randint(int(nf/2+1),nf)
		if nf>=11 and nf<=20: n=random.randint(9,12)
		if nf>=21: n=random.randint(11,14)
	if units <= 20:
		if nf<=10: n=random.randint(int(nf/2+1),nf)
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
	clist=clist[:int(n*num_districts/nf-n)]
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
		clist.append(k)
		if len(clist)==n: break
	return clist

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
		#	 break
	return population2

def SOCP_location_sub_model(sigma, rlevel,timeLimit,mipgap):
	global centersID
	global node_groups
	global facilityCost
	global facilityCapacity    
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
				clist=[x for x in range(num_districts) if centersID[x]<0]
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
				ulist=[x for x in range(num_units) if node_groups[x] in dlist]
				clist=[x for x in NearFacilityList[u] if centersID[x]<0]
				random.shuffle(clist)
		break

	nfnu=len(dlist)*len(ulist)
	ratio=max(1.0,1.0*large_neigborhood_maxIJ/len(ulist)/len(dlist)-1.0)    
	ratio=min(ratio, 5.0) #num of candadates < len(ulist)/2
	#ratio=1.0    
	numcl=len(dlist)*ratio   
	clist=clist[:int(numcl)]
	centers=list(set(clist+dlist))
	#print([len(dlist),ratio,len(centers),len(ulist)])    
	exist_centers=[k for k in range(num_districts) if centersID[k]>=0 and k not in dlist]
	m =gp.Model("_CC_CFLP")
	y = m.addVars(centers, vtype=GRB.BINARY, name="y")                  # 开放设施
	x = m.addVars(ulist, centers+exist_centers, vtype=GRB.BINARY, name="x") 
	z = m.addVars(centers,lb=0.0, name="z") #overload 
	w = m.addVar(lb=0.0, name="w") #max facility budget
	g = m.addVar(lb=0.0, name="g")  #max_covering 
	h = m.addVars(centers, lb=0, vtype=GRB.INTEGER, name="h")  # location size

	#demands=[nodes[i][3] for i in ulist]

	overload=sum(district_info[k][4] for k in dlist)
	penalty=overload
	if max_facility_cost>0:    
		overcost=max(0, sum(facilityCost[k] for k in range(num_districts) if centersID[k]>=0)-max_facility_cost)
		penalty=overload+overcost
	#print([penalty, overload])
	ispenalty=0
	#if penalty>total_pop/1000:     
	#	ispenalty=1
	obj_fun=sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers+exist_centers) 
	if location_problem==1:    
		obj_fun += sum(penalty_on_demand* z[k] for k in centers)  
		if fixed_cost_obj==1:
			obj_fun+= sum(facilityCost[k]*y[k] for k in centers) 
	if location_problem==11:    
		obj_fun+= sum(fnodes[k][5]*y[k] for k in centers) 
		obj_fun+=sum(helicopter_fixed_Cost*h[k] for k in centers)
		obj_fun+=sum(penalty_on_demand*z[k] for k in centers) 
	if cflp_min_service_coverage_percentage>0:
		obj_fun += penalty_on_demand*g
	if max_facility_cost>0:
		obj_fun += penalty_on_demand*w
	m.setObjective(obj_fun, GRB.MINIMIZE)

	#set lowerbound on distance and overload penalty    
	#m.addConstr(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers+exist_centers)>= 0.8*sum(district_info[k][2] for k in dlist), name=f"objlb1")
	#m.addConstr(sum(z[k] for k in centers) >= 0.2*sum(district_info[k][4] for k in dlist), name=f"objlb2")

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")

	for i in ulist:
		for j in centers:
			m.addConstr(x[i,j] <= y[j], name=f"assign_{i}_{j}")

	for i in ulist:
		klist=[k for k in NearFacilityList[i] if k in centers+exist_centers]
		nnn=max(6,int(ratio*4))
		for k in klist[nnn:]:
			if node_groups[i]==k: continue
			m.addConstr(x[i,k] == 0, name=f"xzero_{i}_{k}")

	if adaptive_number_of_facilities==0:
		#fc=sum(1 for k in range(num_districts) if centersID[k]>=0)
		m.addConstr(y.sum() == len(dlist), "open_p")

	if max_facility_cost>0:
		efcost=sum(facilityCost[k] for k in range(num_districts) if centersID[k]>=0 and k not in dlist)
		m.addConstr(sum(facilityCost[k]*y[k] for k in centers) <= w + max_facility_cost-efcost, "open_cost")
		#fcost=max_facility_cost-sum(facilityCost[k] for k in range(num_districts) if centersID[k]>=0 and k not in dlist)        
		#m.addConstr(sum(facilityCost[k]/fcost*y[k] for k in centers) <= 1.0/fcost*w + 1, "open_cost")
	if location_problem==11:
		for j in centers:
			m.addConstr( h[j]<= fnodes[j][6]*y[j], name=f"size_{j}")
        
	za=alpha2z(rlevel)    
	for j in centers:
		s = m.addVar(lb=0.0, name=f"s_{j}")
		quad_expr=gp.QuadExpr()
		for i in ulist:
			quad_expr+=sigma[i]*sigma[i]*x[i,j]
		m.addQConstr(quad_expr <= s*s, name=f"soc_{j}")
		if location_problem==1:
			m.addConstr(sum(nodes[i][3] * x[i,j] for i in ulist) + za * s <= z[j]+facilityCapacity[j] * y[j], name=f"chance_{j}")
		if location_problem==11:
			m.addConstr(sum(nodes[i][3] * x[i,j] for i in ulist) + za * s <= z[j]+helicopter_service_capacity * h[j], name=f"chance_{j}")
		m.addConstr( z[j]<= facilityCapacity[j]*y[j], name=f"ol_{j}")

	for j in exist_centers:
		s = m.addVar(lb=0.0, name=f"s_{j}")
		quad_expr=gp.QuadExpr()
		for i in ulist:
			quad_expr+=sigma[i]*sigma[i]*x[i,j]
		ilist=[i for i in range(num_units) if node_groups[i]==j]
		var=sum(sigma[i]*sigma[i] for i in ilist)
		quad_expr+=var
		supply=facilityCapacity[j]-sum(nodes[i][3] for i in ilist)
		if supply<za*math.sqrt(var): supply=za*math.sqrt(var)
		m.addQConstr(quad_expr <= s*s, name=f"soc_{j}")
		m.addConstr(sum(nodes[i][3] * x[i,j] for i in ulist) + za * s <= supply, name=f"chance_{j}")

	if cflp_min_service_coverage_percentage>0:
		covered=0
		covered1=0
		for i in range(num_units):
			k=node_groups[i]
			if nodedij[i][k]>cflp_service_radius_preference: continue
			if i in ulist: 
				covered1+=nodes[i][3]
			else: covered+=nodes[i][3]
		cover_expr=gp.LinExpr()
		covered2= total_pop/100.0*cflp_min_service_coverage_percentage-covered
		#covered2=min(covered1, covered2)
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>cflp_service_radius_preference: continue
				cover_expr+=nodes[i][3]*x[i,j]
		m.addConstr(cover_expr + g >= covered2, name=f"min_cover")
		#print([total_pop/100.0*cflp_min_service_coverage_percentage,covered,covered1,covered2])
	gap=mipgap
	m.Params.OutputFlag = solver_message  
	m.Params.TimeLimit = timeLimit 
	m.Params.MIPGap = gap
	for k in dlist:
		y[k].start=1.0
		z[k].start=district_info[k][4]
	for i in ulist:
		k=node_groups[i]
		x[i,k].start=1.0
	m.write("_sub_cccflp.lp")
	m.optimize()
	if m.status!=2 and m.status!=9 and m.status!=13: 
		print("infeasible solution!!")
		return neig
	for j in dlist: centersID[j]=-1
	for i in ulist:
		for j in centers+exist_centers:
			if x[i,j].X > 0.5:
				node_groups[i]=j
	for j in centers:
		if y[j].X < 0.5: continue
		centersID[j]=facilityCandidate[j]
		if location_problem==11:
			nh=int(h[j].X+ 0.1)
			fnodes[j][4]=helicopter_service_capacity*nh
			fnodes[j][3]=nh*helicopter_fixed_Cost+fnodes[j][5]
			facilityCost[j]=fnodes[j][5]+helicopter_fixed_Cost*nh
			facilityCapacity[j]=nh*helicopter_service_capacity
	'''for j in centers:
		if h[j].X > 0.5: print("h_",j, h[j].X)
		if z[j].X > 0.5: print("z_",j, z[j].X)
	print("g:",g.X)
	print("w:",w.X)'''
	update_rubust_district_info(sigma,za)
	'''fc=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)    
	fcapa=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0)    
	print("obj,fc,fcapa:",biobjective,fc,fcapa)
	print( [x for x in range(num_districts) if centersID[x]>=0])   
	print( [facilityCost[x] for x in range(num_districts) if centersID[x]>=0])   
	print( [facilityCapacity[x] for x in range(num_districts) if centersID[x]>=0])  '''
	return neig      
	
def SOCP_assign_sub_model(sigma, rlevel, timeLimit,mipgap):
	global centersID
	global node_groups
	global time_LNS1
	t=time.time()
	nf=sum(1 for k in centersID if k>=0)
	if nf <20:
		dlist,clist=select_region_adaptive(-1)
		ulist=[x for x in range(num_units) if node_groups[x] in dlist]
	else:
		dlist=[k for k in range(num_districts) if centersID[k]>=0]
		ulist=range(num_units)
	centers=dlist
	#print(dlist)
	m =gp.Model("CC_CFLP")
	x = m.addVars(ulist, centers, vtype=GRB.BINARY, name="x") 
	z = m.addVars(centers,lb=0.0, name="z")

	if objective_overload<=total_pop/100:
		m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)
					+ sum(penalty_on_demand*z[k] for k in centers), GRB.MINIMIZE)
	else:
		m.setObjective(sum(z[k] for k in centers), GRB.MINIMIZE)

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")

	for i in ulist:
		klist=[k for k in NearFacilityList[i] if k in centers]
		for k in klist[5:]:
			if node_groups[i]==k: continue
			m.addConstr(x[i,k] == 0, name=f"assign_{i}_{k}")

	za=alpha2z(rlevel)    
	for j in centers:
		s = m.addVar(lb=0.0, name=f"s_{j}")
		quad_expr=gp.QuadExpr()
		for i in ulist:
			quad_expr+=sigma[i]*sigma[i]*x[i,j]
		m.addQConstr(quad_expr <= s*s, name=f"soc_{j}")
		m.addConstr(sum(nodes[i][3] * x[i,j] for i in ulist) + za * s <= z[j]+facilityCapacity[j], name=f"chance_{j}")

	m.Params.OutputFlag = solver_message  
	m.Params.TimeLimit = timeLimit 
	m.Params.MIPGap = mipgap
	#m.Params.MIPFocus=0
	for k in centers:
		z[k].start=district_info[k][4]
	for i in ulist:
		k=node_groups[i]
		x[i,k].start=1.0
	m.optimize()
	if m.status!=2 and m.status!=9 and m.status!=13: 
		print("infeasible solution!!")
	for i in ulist:
		for j in centers:
			if x[i,j].X > 0.5:
				node_groups[i]=j
	
#uniform distribution
def overload_possiblity(ulevel,rlevel):
	print ("-------------overload possibility----------------")
	#P(si>sigma_wj) 
	#CDF index 0.0~3.4
	CDF=[0.5,0.5398,0.5793,0.6179,0.6554,0.6915,0.7257,0.758,0.7881,0.8159,
			0.8413,0.8643,0.8849,0.9032,0.9192,0.9332,0.9452,0.9554,0.9641,0.9713,
			0.9772,0.9821,0.9861,0.9893,0.9918,0.9938,0.9953,0.9965,0.9974,0.9981,
			0.9987,0.999,0.9993,0.9995,0.9997,1]
	for k in range(num_districts):
		if district_info[k][0]==0: continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		mean=sum(nodes[x][3] for x in ulist)
		var=sum(nodes[x][3]*ulevel[x]*nodes[x][3]*ulevel[x]/3 for x in ulist)
		std=34
		if var>0:
			std=int((facilityCapacity[k]-mean)/math.sqrt(var)*10)
		if std>34:std=34
		s="facility: "+str(k)+" "+str(district_info[k])+" P(demands<=supply)="+ str(CDF[min(std,34)])
		print (s)

def alpha2z(alpha): 
	robust_level=1-alpha
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
	
def RoCFLP_L2_SOCP_mip(pMetrix,gama,tlimit,mipgap):
	global centersID
	global node_groups
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	m =gp.Model("_RoCFLP_L2")
	y = m.addVars(centers, vtype=GRB.BINARY, name="y") 
	x = m.addVars(ulist, centers, vtype=GRB.BINARY, name="x") 
	t = m.addVars(ulist, centers, lb=0.0, name="t") 
	z = m.addVars(centers,lb=0.0, name="z")
	s = m.addVars(centers,lb=0.0, name="s")
	#w=m.addVar(lb=0.0, name="m")

	if envy_service_objective==0:
		if fixed_cost_obj==0:
			m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)  , GRB.MINIMIZE)
		if fixed_cost_obj==1:
			m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)+sum(facilityCost[k]*y[k] for k in centers), GRB.MINIMIZE)
	if envy_service_objective==1:
		c=[ [0.0 for j in centers] for i in ulist]
		for i in ulist:
			for j in centers:
				d=max(0, nodedij[i][j]-envy_service_distance)
				c[i][j]=travel_distance_weight*nodedik[i][j] + envy_objective_weight*nodes[i][3]*d*d
		m.setObjective(sum(c[i][j] * x[i,j] for i in ulist for j in centers), GRB.MINIMIZE)	

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")

	for i in ulist:
		for j in centers:
			m.addConstr(x[i,j] <= y[j], name=f"assign_{i}_{j}")

	if adaptive_number_of_facilities==0:
		m.addConstr(y.sum() == max_num_facility, "open_p")

	if max_facility_cost>0:
		m.addConstr(sum(facilityCost[k]*y[k] for k in centers) <= max_facility_cost, "open_cost")
	for j in centers:
		for i in ulist:
			m.addQConstr(sum(pMetrix[i][k]*x[k,j] for k in ulist) <= t[i,j], name=f"std_{i}_{j}")

	demands=[nodes[i][3] for i in ulist]
	for j in centers:
		quad_expr=gp.QuadExpr()
		for i in ulist:
			#if nodedij[i][j]>cflp_max_service_radius: continue
			quad_expr+=t[i,j]*t[i,j]
		m.addQConstr(quad_expr <= z[j]*z[j], name=f"soc_{j}")
		m.addConstr(sum(demands[i] * x[i,j] for i in ulist) + gama * z[j] <= facilityCapacity[j] * y[j], name=f"chance_{j}")

	for i in ulist:
		for j in centers:
			if nodedij[i][j]<=cflp_max_service_radius: continue
			m.addConstr(x[i,j] == 0, name=f"assign_zero_{i}_{j}")
	cover_expr=gp.LinExpr()
	if cflp_min_service_coverage_percentage>0:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>cflp_service_radius_preference: continue
				cover_expr+=nodes[i][3]*x[i,j]
		m.addConstr(cover_expr >= total_pop/100.0*cflp_min_service_coverage_percentage, name=f"min_cover")

	if len(node_groups)>0:
		for k in centers:
			if centersID[k]>=0:
				y[k].start=1.0
		for i in ulist:
			k=node_groups[i]
			x[i,k].start=1.0

	m.write("_rocflp_l2.lp")
	m.Params.OutputFlag = solver_message
	m.Params.TimeLimit = tlimit
	m.Params.MIPGap = mipgap
	#m.Params.MIPFocus=0
	#m.Params.NoRelHeurSolutions=5
	m.Params.Heuristics=0.5
	m.optimize()

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]

	for i in ulist:
		for j in centers:
			if x[i,j].X > 0.5:
				node_groups[i]=j
	for j in centers:
		if y[j].X > 0.5:
			centersID[j]=facilityCandidate[j]
	update_district_info()
	return 1      
#robust location and size problem using L2 set
def RoCFLSP_L2_SOCP_mip(pMetrix,gama,tlimit,mipgap):
	global centersID
	global node_groups
	centers=range(num_districts)#facilityCandidate
	ulist=range(num_units)
	m =gp.Model("_RoCFLP_L2")
	w = m.addVars(centers,lb=0,  vtype=GRB.INTEGER,name="w")
	y = m.addVars(centers, vtype=GRB.BINARY, name="y") 
	x = m.addVars(ulist, centers, vtype=GRB.BINARY, name="x") 
	t = m.addVars(ulist, centers, lb=0.0, name="t") 
	z = m.addVars(centers,lb=0.0, name="z")
	#w=m.addVar(lb=0.0, name="m")

	if fixed_cost_obj==0:
		m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)  , GRB.MINIMIZE)
	if fixed_cost_obj==1:
		m.setObjective(sum(nodedik[i][j] * x[i,j] for i in ulist for j in centers)+sum(fnodes[k][5]*y[k] for k in centers)+ sum(helicopter_fixed_Cost*w[k] for k in centers), GRB.MINIMIZE)

	for i in ulist:
		m.addConstr(x.sum(i, '*') == 1, name=f"demand_{i}")

	for i in ulist:
		for j in centers:
			m.addConstr(x[i,j] <= y[j], name=f"assign_{i}_{j}")

	if adaptive_number_of_facilities==0:
		m.addConstr(y.sum() == max_num_facility, "open_p")

	if max_facility_cost>0:
		m.addConstr(sum(facilityCost[k]*y[k] for k in centers) <= max_facility_cost, "open_cost")
	for j in centers:
		for i in ulist:
			m.addQConstr(sum(pMetrix[i][k]*x[k,j] for k in ulist) <= t[i,j], name=f"std_{i}_{j}")

	for j in centers:
		m.addConstr(w[j]<=fnodes[j][6]*y[j],name=f"ub_{j}")

	demands=[nodes[i][3] for i in ulist]
	for j in centers:
		quad_expr=gp.QuadExpr()
		for i in ulist:
			#if nodedij[i][j]>cflp_max_service_radius: continue
			quad_expr+=t[i,j]*t[i,j]
		m.addQConstr(quad_expr <= z[j]*z[j], name=f"soc_{j}")
		m.addConstr(sum(demands[i] * x[i,j] for i in ulist) + gama * z[j] <= helicopter_service_capacity * w[j], name=f"chance_{j}")

	for i in ulist:
		for j in centers:
			if nodedij[i][j]<=cflp_max_service_radius: continue
			m.addConstr(x[i,j] == 0, name=f"assign_zero_{i}_{j}")
	cover_expr=gp.LinExpr()
	if cflp_min_service_coverage_percentage>0:
		for i in ulist:
			for j in centers:
				if nodedij[i][j]>cflp_service_radius_preference: continue
				cover_expr+=nodes[i][3]*x[i,j]
		m.addConstr(cover_expr >= total_pop/100.0*cflp_min_service_coverage_percentage, name=f"min_cover")

	if len(node_groups)>0:
		for k in centers:
			if centersID[k]>=0:
				y[k].start=1.0
			w[j]=int(facilityCapacity[j]/helicopter_service_capacity+0.1)
		for i in ulist:
			k=node_groups[i]
			x[i,k].start=1.0
	m.write("_rocflp.lp")
	m.Params.OutputFlag = solver_message
	m.Params.TimeLimit = tlimit
	m.Params.MIPGap = mipgap
	#m.Params.MIPFocus=0
	#m.Params.NoRelHeurSolutions=5
	m.Params.Heuristics=0.5
	m.optimize()

	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]

	for i in ulist:
		for j in centers:
			if x[i,j].X > 0.5:
				node_groups[i]=j
	for j in centers:
		if y[j].X > 0.5:
			centersID[j]=facilityCandidate[j]
		if w[j].X > 0.5:
			nh=int(w[j].X+0.1)
			fnodes[j][3]=fnodes[j][5]+nh*helicopter_fixed_Cost
			fnodes[j][4]= nh*helicopter_service_capacity
			facilityCost[j]=fnodes[j][3]
			facilityCapacity[j]=fnodes[j][4]
	update_district_info()
	return 1      

def save_demand_file(dnodes,fn):
	f = open(fn,"w")
	idx=0
	f.write("ID\tX\tY\tDemand\tstd\tCenter\n")
	for x in dnodes:
		s=""
		for y in x:
			s+=str(y)+"\t"
		s+="\n" #capa
		f.write(s)
	f.close()

def save_facility_file(fnodes,fn):
	f = open(fn,"w")
	f.write("FID	X	Y	TotalCost	Capacity	BaseCost	MaxHnum	Selected\n")
	for x in fnodes:
		s=""
		for y in x:
			s+=str(y)+"\t"
		s+="\n" #capa
		f.write(s)
	f.close()

def coverage_stat_hems(dlist,kset):
	clist=[(nodedij[x][node_groups[x]]-helicopter_flight_fixed_cost)/helicopter_flight_hour_cost*helicopter_speed_hour for x in range(num_units)]
	#clist=[nodedij[x][node_groups[x]] for x in range(num_units)]
	s=str(["meanD:", sum(nodes[x][3]*clist[x] for x in range(num_units))/total_pop, " maxD:", max(clist)])
	covered=[0,0,0,0]
	for i in range(num_units):
		dis=clist[i]
		demand=nodes[i][3]
		if dis<=dlist[0]:	 covered[0]+=demand
		if dis<=dlist[1]:	 covered[1]+=demand
		if dis<=dlist[2]:	 covered[2]+=demand
		if dis<=dlist[3]: covered[3]+=demand
	for i in range(4):
		s+=str([dlist[i],int(covered[i]*10000.0/total_pop)/100.0,"%"])
	print(s)
