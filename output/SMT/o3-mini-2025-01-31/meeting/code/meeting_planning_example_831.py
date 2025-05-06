from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location indices:
# 0: Presidio (starting point)
# 1: Fisherman's Wharf
# 2: Alamo Square
# 3: Financial District
# 4: Union Square
# 5: Sunset District
# 6: Embarcadero
# 7: Golden Gate Park
# 8: Chinatown
# 9: Richmond District

# Travel distances (in minutes) between locations:
travel = {
    # Presidio (0)
    (0,1): 19, (0,2): 19, (0,3): 23, (0,4): 22, (0,5): 15, (0,6): 20, (0,7): 12, (0,8): 21, (0,9): 7,
    # Fisherman's Wharf (1)
    (1,0): 17, (1,2): 21, (1,3): 11, (1,4): 13, (1,5): 27, (1,6): 8,  (1,7): 25, (1,8): 12, (1,9): 18,
    # Alamo Square (2)
    (2,0): 17, (2,1): 19, (2,3): 17, (2,4): 14, (2,5): 16, (2,6): 16, (2,7): 9,  (2,8): 15, (2,9): 11,
    # Financial District (3)
    (3,0): 22, (3,1): 10, (3,2): 17, (3,4): 9,  (3,5): 30, (3,6): 4,  (3,7): 23, (3,8): 5,  (3,9): 21,
    # Union Square (4)
    (4,0): 24, (4,1): 15, (4,2): 15, (4,3): 9,  (4,5): 27, (4,6): 11, (4,7): 22, (4,8): 7,  (4,9): 20,
    # Sunset District (5)
    (5,0): 16, (5,1): 29, (5,2): 17, (5,3): 30, (5,4): 30, (5,6): 30, (5,7): 11, (5,8): 30, (5,9): 12,
    # Embarcadero (6)
    (6,0): 20, (6,1): 6,  (6,2): 19, (6,3): 5,  (6,4): 10, (6,5): 30, (6,7): 25, (6,8): 7,  (6,9): 21,
    # Golden Gate Park (7)
    (7,0): 11, (7,1): 24, (7,2): 9,  (7,3): 26, (7,4): 22, (7,5): 10, (7,6): 25, (7,8): 23, (7,9): 7,
    # Chinatown (8)
    (8,0): 19, (8,1): 8,  (8,2): 17, (8,3): 5,  (8,4): 7,  (8,5): 29, (8,6): 5,  (8,7): 23, (8,9): 20,
    # Richmond District (9)
    (9,0): 7,  (9,1): 18, (9,2): 13, (9,3): 22, (9,4): 21, (9,5): 11, (9,6): 19, (9,7): 9,  (9,8): 20,
}

# Friend meeting information.
# Each tuple: (location, avail_start, avail_end, min_duration)
# Times are minutes after midnight.
#
# Jeffrey  at Fisherman's Wharf (loc 1): 10:15AM (615) to 1:00PM (780),     min 90 minutes.
# Ronald   at Alamo Square (loc 2):      7:45AM (465) to 2:45PM (885),      min 120 minutes.
# Jason    at Financial District (loc 3): 10:45AM (645) to 4:00PM (960),     min 105 minutes.
# Melissa  at Union Square (loc 4):       5:45PM (1065) to 6:15PM (1095),    min 15 minutes.
# Elizabeth at Sunset District (loc 5):     2:45PM (885) to 5:30PM (1050),    min 105 minutes.
# Margaret at Embarcadero (loc 6):        1:15PM (795) to 7:00PM (1140),     min 90 minutes.
# George   at Golden Gate Park (loc 7):     7:00PM (1140) to 10:00PM (1320),   min 75 minutes.
# Richard  at Chinatown (loc 8):           9:30AM (570) to 9:00PM (1260),     min 15 minutes.
# Laura    at Richmond District (loc 9):   9:45AM (585) to 6:00PM (1080),      min 60 minutes.
friends = [
    (1, 615, 780, 90),   # Jeffrey
    (2, 465, 885, 120),  # Ronald
    (3, 645, 960, 105),  # Jason
    (4, 1065, 1095, 15), # Melissa
    (5, 885, 1050, 105), # Elizabeth
    (6, 795, 1140, 90),  # Margaret
    (7, 1140, 1320, 75), # George
    (8, 570, 1260, 15),  # Richard
    (9, 585, 1080, 60)   # Laura
]
num_friends = len(friends)

# Starting condition: you arrive at Presidio (loc 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Optimize instance.
opt = Optimize()

# Decision variables:
# x[i]: Boolean indicating if you meet friend i.
# A[i]: Arrival time (in minutes) at friend i's location.
# order[i]: Meeting order (if scheduled, an integer from 0 to num_friends-1; otherwise forced to -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If friend i is met then order[i] is between 0 and num_friends-1; else order[i] == -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order values for friends that are scheduled.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# For each friend i, let effective_start = max(A[i], avail_start). Then effective_start + min_duration <= avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + dur <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), arrival time must be at least start_time plus travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings: if friend j is scheduled immediately after friend i then:
# arrival_time for friend j must be at least (max(A[i], avail_start of i) + dur_i) + travel_time from friend i to friend j.
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

# Solve and display the optimal meeting schedule.
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
    
    friend_names = ["Jeffrey", "Ronald", "Jason", "Melissa", "Elizabeth", "Margaret", "George", "Richard", "Laura"]
    loc_names = {
        0: "Presidio",
        1: "Fisherman's Wharf",
        2: "Alamo Square",
        3: "Financial District",
        4: "Union Square",
        5: "Sunset District",
        6: "Embarcadero",
        7: "Golden Gate Park",
        8: "Chinatown",
        9: "Richmond District"
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