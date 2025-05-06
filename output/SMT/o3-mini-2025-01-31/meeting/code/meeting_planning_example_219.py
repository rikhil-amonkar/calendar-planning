from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Locations (indices):
# 0: The Castro (starting point)
# 1: Alamo Square
# 2: Union Square
# 3: Chinatown

# Travel times (in minutes) between locations.
# Note: travel times are directional.
travel = {
    (0,1): 8,   (0,2): 19,  (0,3): 20,
    (1,0): 8,   (1,2): 14,  (1,3): 16,
    (2,0): 19,  (2,1): 15,  (2,3): 7,
    (3,0): 22,  (3,1): 17,  (3,2): 7
}

# Friend meeting information:
# Each tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Emily at Alamo Square (loc 1): 11:45AM (705) to 3:15PM (915), min 105 minutes.
# Barbara at Union Square (loc 2): 4:45PM (1005) to 6:15PM (1095), min 60 minutes.
# William at Chinatown (loc 3): 5:15PM (1035) to 7:00PM (1140), min 105 minutes.
friends = [
    (1, 705, 915, 105),   # Emily
    (2, 1005, 1095, 60),   # Barbara
    (3, 1035, 1140, 105)   # William
]
num_friends = len(friends)

# Starting conditions: You arrive at The Castro (loc 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Z3 optimizer instance.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]: Bool that indicates if meeting friend i is scheduled.
#   A[i]: Arrival time (in minutes) at the friend's location.
#   order[i]: The meeting order if scheduled (an integer from 0 to num_friends-1), otherwise -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If scheduled then order is between 0 and num_friends-1, otherwise -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# Enforce distinct meeting orders for any two scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend scheduled, the meeting starts at max(arrival, avail_start)
# and the meeting (start + min_duration) must finish before avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + dur <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), you travel from your starting location (The Castro).
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j is scheduled immediately after friend i,
# then arrival time A[j] must be at least the departure time from friend i plus travel time.
# Here, departure time from friend i is: max(A[i], avail_start of friend i) + meeting duration of friend i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        depart_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= depart_i + travel_time))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
        
    friend_names = ["Emily", "Barbara", "William"]
    loc_names = {
        0: "The Castro",
        1: "Alamo Square",
        2: "Union Square",
        3: "Chinatown"
    }
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")