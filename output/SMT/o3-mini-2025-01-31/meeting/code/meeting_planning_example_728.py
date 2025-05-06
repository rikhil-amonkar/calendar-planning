from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location indices:
# 0: Marina District (starting point)
# 1: Mission District
# 2: Fisherman's Wharf
# 3: Presidio
# 4: Union Square
# 5: Sunset District
# 6: Financial District
# 7: Haight-Ashbury
# 8: Russian Hill

# Travel distances (in minutes) between locations.
travel = {
    # From Marina District (0)
    (0,1): 20, (0,2): 10, (0,3): 10, (0,4): 16, (0,5): 19, (0,6): 17, (0,7): 16, (0,8): 8,
    # From Mission District (1)
    (1,0): 19, (1,2): 22, (1,3): 25, (1,4): 15, (1,5): 24, (1,6): 15, (1,7): 12, (1,8): 15,
    # From Fisherman's Wharf (2)
    (2,0): 9,  (2,1): 22, (2,3): 17, (2,4): 13, (2,5): 27, (2,6): 11, (2,7): 22, (2,8): 7,
    # From Presidio (3)
    (3,0): 11, (3,1): 26, (3,2): 19, (3,4): 22, (3,5): 15, (3,6): 23, (3,7): 15, (3,8): 14,
    # From Union Square (4)
    (4,0): 18, (4,1): 14, (4,2): 15, (4,3): 24, (4,5): 27, (4,6): 9,  (4,7): 18, (4,8): 13,
    # From Sunset District (5)
    (5,0): 21, (5,1): 25, (5,2): 29, (5,3): 16, (5,4): 30, (5,6): 30, (5,7): 15, (5,8): 24,
    # From Financial District (6)
    (6,0): 15, (6,1): 17, (6,2): 10, (6,3): 22, (6,4): 9,  (6,5): 30, (6,7): 19, (6,8): 11,
    # From Haight-Ashbury (7)
    (7,0): 17, (7,1): 11, (7,2): 23, (7,3): 15, (7,4): 19, (7,5): 15, (7,6): 21, (7,8): 17,
    # From Russian Hill (8)
    (8,0): 7,  (8,1): 16, (8,2): 7,  (8,3): 14, (8,4): 10, (8,5): 23, (8,6): 11, (8,7): 17
}

# Friend meeting information.
# Each tuple: (location, avail_start, avail_end, min_duration)
# Times are minutes after midnight.
#
# Karen:      Mission District (loc 1) from 2:15PM (855) to 10:00PM (1320), min 30 minutes.
# Richard:    Fisherman's Wharf (loc 2) from 2:30PM (870) to 5:30PM (1050), min 30 minutes.
# Robert:     Presidio (loc 3) from 9:45PM (1305) to 10:45PM (1365), min 60 minutes.
# Joseph:     Union Square (loc 4) from 11:45AM (705) to 2:45PM (885), min 120 minutes.
# Helen:      Sunset District (loc 5) from 2:45PM (885) to 8:45PM (1305), min 105 minutes.
# Elizabeth:  Financial District (loc 6) from 10:00AM (600) to 12:45PM (765), min 75 minutes.
# Kimberly:   Haight-Ashbury (loc 7) from 2:15PM (855) to 5:30PM (1050), min 105 minutes.
# Ashley:     Russian Hill (loc 8) from 11:30AM (690) to 9:30PM (1290), min 45 minutes.
friends = [
    (1, 855, 1320, 30),   # Karen
    (2, 870, 1050, 30),   # Richard
    (3, 1305, 1365, 60),  # Robert
    (4, 705, 885, 120),   # Joseph
    (5, 885, 1305, 105),  # Helen
    (6, 600, 765, 75),    # Elizabeth
    (7, 855, 1050, 105),  # Kimberly
    (8, 690, 1290, 45)    # Ashley
]
num_friends = len(friends)

# Starting condition: You arrive at Marina District (loc 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Optimize instance.
opt = Optimize()

# Decision variables:
# x[i]: Boolean indicating whether you meet friend i.
# A[i]: Arrival time at friend i's location.
# order[i]: Meeting order (integer from 0 to num_friends-1 if scheduled, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If friend i is met, then order[i] is in 0...num_friends-1; otherwise, force order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order numbers for meetings that are chosen.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# For each friend i, the effective meeting start is max(A[i], avail_start).
# Then effective_start plus meeting duration must not exceed avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + dur <= avail_end))

# Travel constraints:
# For the first meeting in the order (order == 0), arrival time must be at least start_time plus travel time from start.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings: if friend j is scheduled immediately after friend i, then:
# arrival time at friend j must be at least the departure time from friend i plus travel time.
# Define departure time from friend i as: max(A[i], avail_start of friend i) + meeting duration.
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

# Solve and print the optimal schedule.
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

    friend_names = ["Karen", "Richard", "Robert", "Joseph", "Helen", "Elizabeth", "Kimberly", "Ashley"]
    loc_names = {
        0: "Marina District",
        1: "Mission District",
        2: "Fisherman's Wharf",
        3: "Presidio",
        4: "Union Square",
        5: "Sunset District",
        6: "Financial District",
        7: "Haight-Ashbury",
        8: "Russian Hill"
    }
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Ensure meeting starts no earlier than local avail_start
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")