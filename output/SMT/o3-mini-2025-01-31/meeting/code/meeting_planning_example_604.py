from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location indices:
# 0: Fisherman's Wharf (starting point)
# 1: The Castro
# 2: Golden Gate Park
# 3: Embarcadero
# 4: Russian Hill
# 5: Nob Hill
# 6: Alamo Square
# 7: North Beach

# Travel times (in minutes) between locations (directional).
travel = {
    (0,1): 26, (0,2): 25, (0,3): 8,  (0,4): 7,  (0,5): 11, (0,6): 20, (0,7): 6,
    
    (1,0): 24, (1,2): 11, (1,3): 22, (1,4): 18, (1,5): 16, (1,6): 8,  (1,7): 20,
    
    (2,0): 24, (2,1): 13, (2,3): 25, (2,4): 21, (2,5): 20, (2,6): 10, (2,7): 24,
    
    (3,0): 6,  (3,1): 25, (3,2): 25, (3,4): 8,  (3,5): 10, (3,6): 19, (3,7): 5,
    
    (4,0): 7,  (4,1): 21, (4,2): 21, (4,3): 8,  (4,5): 5,  (4,6): 15, (4,7): 5,
    
    (5,0): 11, (5,1): 17, (5,2): 17, (5,3): 9,  (5,4): 5,  (5,6): 11, (5,7): 8,
    
    (6,0): 19, (6,1): 8,  (6,2): 9,  (6,3): 17, (6,4): 13, (6,5): 11, (6,7): 15,
    
    (7,0): 5,  (7,1): 22, (7,2): 22, (7,3): 6,  (7,4): 4,  (7,5): 7,  (7,6): 16
}

# Friend meeting information:
# Each tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Laura: at The Castro (loc 1) from 7:45PM to 9:30PM (1185, 1290), min 105 minutes.
# Daniel: at Golden Gate Park (loc 2) from 9:15PM to 9:45PM (1275, 1305), min 15 minutes.
# William: at Embarcadero (loc 3) from 7:00AM to 9:00AM (420, 540), min 90 minutes.
# Karen: at Russian Hill (loc 4) from 2:30PM to 7:45PM (870, 1185), min 30 minutes.
# Stephanie: at Nob Hill (loc 5) from 7:30AM to 9:30AM (450, 570), min 45 minutes.
# Joseph: at Alamo Square (loc 6) from 11:30AM to 12:45PM (690, 765), min 15 minutes.
# Kimberly: at North Beach (loc 7) from 3:45PM to 7:15PM (945, 1155), min 30 minutes.
friends = [
    (1, 1185, 1290, 105),  # Laura
    (2, 1275, 1305, 15),   # Daniel
    (3, 420, 540, 90),     # William
    (4, 870, 1185, 30),    # Karen
    (5, 450, 570, 45),     # Stephanie
    (6, 690, 765, 15),     # Joseph
    (7, 945, 1155, 30)     # Kimberly
]
num_friends = len(friends)

# Starting conditions: You arrive at Fisherman's Wharf (loc 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Z3 optimizer instance.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i]: Bool indicating if you choose to meet friend i.
#   A[i]: Int for the arrival time at friend i's location.
#   order[i]: Int for the ordering of the meeting (if scheduled: 0...num_friends-1; otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Enforce that if friend i is scheduled, order[i] is in 0...num_friends-1, else it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure scheduled meetings get distinct ordering.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# The meeting for friend i starts at max(arrival time, avail_start) and lasts min_duration minutes.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + dur <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), you must travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j follows friend i, then the arrival time for j must be after
# the departure time from i plus travel time between i and j.
# Departure time for friend i is: max(A[i], avail_start_i) + min_duration_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + t_time))

# Objective: maximize the total number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the meeting schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings along with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append( (model.evaluate(order[i]).as_long(), i) )
    schedule.sort()  # sort by meeting order

    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Laura", "Daniel", "William", "Karen", "Stephanie", "Joseph", "Kimberly"]
    loc_names = {
        0: "Fisherman's Wharf",
        1: "The Castro",
        2: "Golden Gate Park",
        3: "Embarcadero",
        4: "Russian Hill",
        5: "Nob Hill",
        6: "Alamo Square",
        7: "North Beach"
    }
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts at the later of arrival and the friend’s available start time.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")