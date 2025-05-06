from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Locations (indices):
# 0: Union Square (starting point)
# 1: Russian Hill
# 2: Alamo Square
# 3: Haight-Ashbury
# 4: Marina District
# 5: Bayview
# 6: Chinatown
# 7: Presidio
# 8: Sunset District

# Travel distances (in minutes) between locations.
# Note: They are directional (the value from A to B may differ from B to A)
travel = {
    # From Union Square (0)
    (0,1): 13, (0,2): 15, (0,3): 18, (0,4): 18, (0,5): 15, (0,6): 7,  (0,7): 24, (0,8): 27,
    # From Russian Hill (1)
    (1,0): 10, (1,2): 15, (1,3): 17, (1,4): 7,  (1,5): 23, (1,6): 9,  (1,7): 14, (1,8): 23,
    # From Alamo Square (2)
    (2,0): 14, (2,1): 13, (2,3): 5,  (2,4): 15, (2,5): 16, (2,6): 15, (2,7): 17, (2,8): 16,
    # From Haight-Ashbury (3)
    (3,0): 19, (3,1): 17, (3,2): 5,  (3,4): 17, (3,5): 18, (3,6): 19, (3,7): 15, (3,8): 15,
    # From Marina District (4)
    (4,0): 16, (4,1): 8,  (4,2): 15, (4,3): 16, (4,5): 27, (4,6): 15, (4,7): 10, (4,8): 19,
    # From Bayview (5)
    (5,0): 18, (5,1): 23, (5,2): 16, (5,3): 19, (5,4): 27, (5,6): 19, (5,7): 32, (5,8): 23,
    # From Chinatown (6)
    (6,0): 7,  (6,1): 7,  (6,2): 17, (6,3): 19, (6,4): 12, (6,5): 20, (6,7): 19, (6,8): 29,
    # From Presidio (7)
    (7,0): 22, (7,1): 14, (7,2): 19, (7,3): 15, (7,4): 11, (7,5): 31, (7,6): 21, (7,8): 15,
    # From Sunset District (8)
    (8,0): 30, (8,1): 24, (8,2): 17, (8,3): 15, (8,4): 21, (8,5): 22, (8,6): 30, (8,7): 16
}

# Friend meeting information.
# Each tuple is: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    (1, 420, 1005, 105),  # Betty at Russian Hill: 7:00AM to 4:45PM, min 105 min.
    (2, 570, 1035, 105),  # Melissa at Alamo Square: 9:30AM to 5:15PM, min 105 min.
    (3, 735, 1140, 90),   # Joshua at Haight-Ashbury: 12:15PM to 7:00PM, min 90 min.
    (4, 735, 1080, 45),   # Jeffrey at Marina District: 12:15PM to 6:00PM, min 45 min.
    (5, 450, 1200, 90),   # James at Bayview: 7:30AM to 8:00PM, min 90 min.
    (6, 705, 810, 75),    # Anthony at Chinatown: 11:45AM to 1:30PM, min 75 min.
    (7, 750, 885, 90),    # Timothy at Presidio: 12:30PM to 2:45PM, min 90 min.
    (8, 1170, 1290, 120)  # Emily at Sunset District: 7:30PM to 9:30PM, min 120 min.
]
num_friends = len(friends)

# Starting conditions: You arrive at Union Square (loc 0) at 9:00AM (540 minutes).
start_loc = 0
start_time = 540

# Create the Z3 optimizer instance.
opt = Optimize()

# Decision Variables:
# For each friend i:
#  - x[i] is a Bool that is True if you choose to meet friend i.
#  - A[i] is an Int representing your arrival time (in minutes) at friend i's location.
#  - order[i] is an Int representing the meeting order (if scheduled, in {0,1,...,num_friends-1}; otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If friend i is scheduled (x[i]==True) then order[i] must be between 0 and num_friends-1;
# if not scheduled, force order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Distinct meeting order for scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints for each friend.
# The meeting will actually start at max(arrival, avail_start) and must finish (start + duration) before avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + dur <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), you must travel from the start location to the meeting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # Travel time from Union Square (start_loc 0) to friend i's location.
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings: if friend j is scheduled immediately after friend i,
# then the arrival time for friend j must be at least the departure time from friend i plus travel time.
# We define the departure time from friend i as: max(A[i], avail_start) + meeting_duration.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by meeting order

    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Betty", "Melissa", "Joshua", "Jeffrey", "James", "Anthony", "Timothy", "Emily"]
    loc_names = {
        0: "Union Square",
        1: "Russian Hill",
        2: "Alamo Square",
        3: "Haight-Ashbury",
        4: "Marina District",
        5: "Bayview",
        6: "Chinatown",
        7: "Presidio",
        8: "Sunset District"
    }
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting cannot start before avail_start; if arrived earlier, you wait.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")