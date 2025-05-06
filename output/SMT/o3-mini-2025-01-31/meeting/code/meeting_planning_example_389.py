from z3 import Optimize, Int, Bool, If, And, Or, Distinct, Sum, sat

# Our locations (neighborhoods) are represented by numbers as follows:
# 0: Haight-Ashbury (start)
# 1: Fisherman's Wharf   (Sarah)
# 2: Richmond District   (Mary)
# 3: Mission District    (Helen)
# 4: Bayview             (Thomas)
#
# Travel times in minutes as given (all times are one‐way, in minutes):
travel = {
    (0,1): 23, (0,2): 10, (0,3): 11, (0,4): 18,
    (1,0): 22, (1,2): 18, (1,3): 22, (1,4): 26,
    (2,0): 10, (2,1): 18, (2,3): 20, (2,4): 26,
    (3,0): 12, (3,1): 22, (3,2): 20, (3,4): 15,
    (4,0): 19, (4,1): 25, (4,2): 25, (4,3): 13
}
# We map friend index to their meeting location:
# Friend 0: Sarah at Fisherman's Wharf  -> location 1
# Friend 1: Mary at Richmond District    -> location 2
# Friend 2: Helen at Mission District     -> location 3
# Friend 3: Thomas at Bayview             -> location 4
loc_mapping = [1, 2, 3, 4]

# Friend meeting availability (in minutes from midnight):
# We use 24-hr times converted to minutes.
# Sarah:  2:45PM = 14*60+45 = 885,  5:30PM = 17*60+30 =1050, need >=105 min
# Mary:   1:00PM = 13*60 = 780,      7:15PM = 19*60+15=1155, need >=75  min
# Helen:  9:45PM = 21*60+45=1305,     10:30PM = 22*60+30=1350, need >=30  min
# Thomas: 3:15PM = 15*60+15=915,      6:45PM = 18*60+45=1125, need >=120 min
avail_start = [885, 780, 1305, 915]
avail_end   = [1050,1155,1350,1125]
meet_min    = [105, 75, 30, 120]

# Start time at Haight-Ashbury (9:00AM = 9*60 = 540)
start_time = 540

# There are 4 friends. For each friend i, we decide whether to meet them (x[i]=True),
# choose an arrival time A[i] (in minutes), and if met assign an order position (order[i])
# in the visiting sequence.
num_friends = 4

opt = Optimize()

# Decision variables
x = [ Bool(f"x_{i}") for i in range(num_friends) ]  # True if we meet friend i
A = [ Int(f"A_{i}") for i in range(num_friends) ]    # arrival time at friend i's location
order = [ Int(f"order_{i}") for i in range(num_friends) ]  # order in route if met; if not, we set to -1

# For each friend, if x[i] is false then set order[i] = -1.
for i in range(num_friends):
    opt.add( Or( x[i] == False, order[i] >= 0 ) )
    opt.add( Or( Not(x[i]), order[i] == -1 ) )  # if not chosen -> order = -1
    # if chosen then order between 0 and num_friends-1
    opt.add( If(x[i], And(order[i] >= 0, order[i] <= num_friends-1), order[i] == -1) )
    # arrival times must be after start of day
    opt.add( A[i] >= 0 )

# For the friends that are chosen, the order numbers must be all different.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        # If both chosen then order[i] != order[j]
        opt.add( Or( Not(x[i]), Not(x[j]), order[i] != order[j] ) )

# Meeting timing constraints for each friend.
for i in range(num_friends):
    # Compute effective meeting start: if you arrive before friend is available, you wait.
    M = If(A[i] < avail_start[i], avail_start[i], A[i])
    # If meeting is held then it must finish by avail_end:
    opt.add( Or( Not(x[i]), M + meet_min[i] <= avail_end[i] ) )

# Travel constraints:
# If a friend is visited first (order==0), travel from Haight-Ashbury to that location is required.
for i in range(num_friends):
    loc_i = loc_mapping[i]
    travel_from_start = travel[(0, loc_i)]
    opt.add( Or( Not(x[i]), order[i] != 0, A[i] >= start_time + travel_from_start ) )

# For every pair of friends, if they are consecutive in the route (i.e. order[j] = order[i] + 1),
# then the arrival time at friend j must be at least the departure time from friend i plus travel time.
# Departure time from friend i is (If(A_i < avail_start, then avail_start, else A_i) + meet_min[i]).
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        travel_ij = travel[(loc_mapping[i], loc_mapping[j])]
        # When friend i and friend j are consecutive in the route (and both chosen)
        # then: A[j] >= (max(A[i], avail_start[i]) + meet_min[i] + travel_ij)
        M_i = If(A[i] < avail_start[i], avail_start[i], A[i])
        cond = And( x[i], x[j], order[j] == order[i] + 1 )
        opt.add( Or( Not(cond), A[j] >= M_i + meet_min[i] + travel_ij ) )

# (Optional) In case there are gaps, we can force the order numbers to be contiguous.
# For each chosen friend, if the maximum order among chosen is k, then every number from 0 to k is used.
# This is automatic if we maximize the number of friends, but we add a weak constraint.
# For every possible order number r from 0 to num_friends-1, if there is a friend with order r, then
# for every r' < r there is also one.
# This is not strictly necessary.

# Objective: maximize the number of friends met.
opt.maximize( Sum([ If(x[i], 1, 0) for i in range(num_friends) ]))

# Solve and print optimal model.
if opt.check() == sat:
    model = opt.model()
    visited = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            visited.append((model.evaluate(order[i]).as_long(), i))
    visited.sort()  # sort by route order
    print("Optimal schedule:")
    for order_val, i in visited:
        arrival = model.evaluate(A[i]).as_long()
        # effective meeting start is max(arrival, avail_start)
        meeting_start = arrival if arrival >= avail_start[i] else avail_start[i]
        meeting_end = meeting_start + meet_min[i]
        # Convert minutes back to HH:MM
        def to_time(t):
            h = t // 60
            m = t % 60
            return f"{h:02d}:{m:02d}"
        loc_names = ["Fisherman's Wharf (Sarah)", "Richmond District (Mary)", 
                     "Mission District (Helen)", "Bayview (Thomas)"]
        print(f" Order {order_val}: Meet {loc_names[i]}")
        print(f"   Arrival: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    num_met = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", num_met)
else:
    print("No feasible schedule found.")