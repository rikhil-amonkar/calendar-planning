from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define locations with indices:
# 0: Bayview
# 1: Pacific Heights
# 2: Mission District
# 3: Haight-Ashbury
# 4: Financial District

# Travel distances (in minutes) between locations as provided:
travel = {
    (0,1): 23, (0,2): 13, (0,3): 19, (0,4): 19,
    (1,0): 22, (1,2): 15, (1,3): 11, (1,4): 13,
    (2,0): 15, (2,1): 16, (2,3): 12, (2,4): 17,
    (3,0): 18, (3,1): 12, (3,2): 11, (3,4): 21,
    (4,0): 19, (4,1): 13, (4,2): 17, (4,3): 19
}

# Friends meeting information:
# Each friend is a tuple of (location, available_start, available_end, minimum_meeting_duration)
# Times are expressed in minutes after midnight.
#
# Mary    at Pacific Heights (loc 1): from 10:00AM (600) to 7:00PM (1140), min 45 minutes.
# Lisa    at Mission District (loc 2):  from 8:30PM (1230) to 10:00PM (1320), min 75 minutes.
# Betty   at Haight-Ashbury (loc 3):    from 7:15AM (435) to 5:15PM (1035), min 90 minutes.
# Charles at Financial District (loc 4):  from 11:15AM (675) to 3:00PM (900), min 120 minutes.
friends = [
    (1, 600, 1140, 45),    # Mary
    (2, 1230, 1320, 75),   # Lisa
    (3, 435, 1035, 90),    # Betty
    (4, 675, 900, 120)     # Charles
]
num_friends = len(friends)

# Start at Bayview (location 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Optimize instance for the Z3 solver.
opt = Optimize()

# Decision variables:
# For each friend i:
#    x[i]   is a boolean indicating if we choose to meet friend i.
#    A[i]   is the arrival time (in minutes) at friend i's location.
#    order[i] is an integer denoting the meeting order position if meeting friend i;
#             if friend i is not met, we force order[i] = -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constraint: if you choose to meet friend i then order[i] is in the range 0 to num_friends-1,
# otherwise set order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# If two friends are both chosen, they must have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting window and minimum duration constraints:
# If friend i is met, we define the effective meeting start as the maximum of the arrival time and the friend’s available start time.
# Then, effective meeting start + meeting duration must be <= available end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + meet_min <= avail_end))

# Travel constraints:
# For the first meeting in the itinerary (order == 0), we must travel from the starting location (Bayview).
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings:
# If friend j is scheduled immediately after friend i (i.e. order[j] == order[i] + 1), then the arrival time for friend j
# must be at least the departure time from friend i plus the travel time from friend i's location to friend j's location.
# The departure time from friend i is computed as max(A[i], avail_start of friend i) + meeting duration for friend i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, meet_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + meet_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and then print the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    # Sort chosen meetings according to their order.
    chosen.sort()
    
    print("Optimal meeting schedule:")
    
    def to_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"
    
    # Map location indices to names and friend indices to friend names.
    loc_names = {
        0: "Bayview",
        1: "Pacific Heights",
        2: "Mission District",
        3: "Haight-Ashbury",
        4: "Financial District"
    }
    friend_names = ["Mary", "Lisa", "Betty", "Charles"]
    
    for ord_val, i in chosen:
        loc, avail_start, avail_end, meet_min = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + meet_min
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total_met = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_met)
else:
    print("No feasible meeting schedule found.")