from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define location indices:
# 0: Haight-Ashbury   (starting point)
# 1: Mission District
# 2: Union Square
# 3: Pacific Heights
# 4: Bayview
# 5: Fisherman's Wharf
# 6: Marina District
# 7: Richmond District
# 8: Sunset District
# 9: Golden Gate Park

# Travel distances (in minutes) between locations.
# Every key (i, j) represents travel time from location i to location j.
travel = {
    # From Haight-Ashbury (0)
    (0,1): 11, (0,2): 19, (0,3): 12, (0,4): 18, (0,5): 23, (0,6): 17, (0,7): 10, (0,8): 15, (0,9): 7,
    # From Mission District (1)
    (1,0): 12, (1,2): 15, (1,3): 16, (1,4): 14, (1,5): 22, (1,6): 19, (1,7): 20, (1,8): 24, (1,9): 17,
    # From Union Square (2)
    (2,0): 18, (2,1): 14, (2,3): 15, (2,4): 15, (2,5): 15, (2,6): 18, (2,7): 20, (2,8): 27, (2,9): 22,
    # From Pacific Heights (3)
    (3,0): 11, (3,1): 15, (3,2): 12, (3,4): 22, (3,5): 13, (3,6): 6,  (3,7): 12, (3,8): 21, (3,9): 15,
    # From Bayview (4)
    (4,0): 19, (4,1): 13, (4,2): 18, (4,3): 23, (4,5): 25, (4,6): 27, (4,7): 25, (4,8): 23, (4,9): 22,
    # From Fisherman's Wharf (5)
    (5,0): 22, (5,1): 22, (5,2): 13, (5,3): 12, (5,4): 26, (5,6): 9,  (5,7): 18, (5,8): 27, (5,9): 25,
    # From Marina District (6)
    (6,0): 16, (6,1): 20, (6,2): 16, (6,3): 7,  (6,4): 27, (6,5): 10, (6,7): 11, (6,8): 19, (6,9): 18,
    # From Richmond District (7)
    (7,0): 10, (7,1): 20, (7,2): 21, (7,3): 10, (7,4): 27, (7,5): 18, (7,6): 9,  (7,8): 11, (7,9): 9,
    # From Sunset District (8)
    (8,0): 15, (8,1): 25, (8,2): 30, (8,3): 21, (8,4): 22, (8,5): 29, (8,6): 21, (8,7): 12, (8,9): 11,
    # From Golden Gate Park (9)
    (9,0): 7,  (9,1): 17, (9,2): 22, (9,3): 16, (9,4): 23, (9,5): 24, (9,6): 16, (9,7): 7,  (9,8): 10
}

# Friends meeting information.
# Each tuple contains:
#   (location, available_start, available_end, minimum_meeting_duration)
# Times are in minutes after midnight.
#
# Elizabeth  at Mission District (loc 1): from 10:30AM (630) to 8:00PM (1200), min 90 minutes.
# David      at Union Square (loc 2):      from 3:15PM (915) to 7:00PM (1140), min 45 minutes.
# Sandra     at Pacific Heights (loc 3):   from 7:00AM (420) to 8:00PM (1200), min 120 minutes.
# Thomas     at Bayview (loc 4):           from 7:30PM (1170) to 8:30PM (1230), min 30 minutes.
# Robert     at Fisherman's Wharf (loc 5): from 10:00AM (600) to 3:00PM (900), min 15 minutes.
# Kenneth    at Marina District (loc 6):    from 10:45AM (645) to 1:00PM (780), min 45 minutes.
# Melissa    at Richmond District (loc 7):   from 6:15PM (1095) to 8:00PM (1200), min 15 minutes.
# Kimberly   at Sunset District (loc 8):     from 10:15AM (615) to 6:15PM (1095), min 105 minutes.
# Amanda     at Golden Gate Park (loc 9):    from 7:45AM (465) to 6:45PM (1105), min 15 minutes.
friends = [
    (1, 630, 1200, 90),   # Elizabeth
    (2, 915, 1140, 45),   # David
    (3, 420, 1200, 120),  # Sandra
    (4, 1170, 1230, 30),  # Thomas
    (5, 600, 900, 15),    # Robert
    (6, 645, 780, 45),    # Kenneth
    (7, 1095, 1200, 15),  # Melissa
    (8, 615, 1095, 105),  # Kimberly
    (9, 465, 1105, 15)    # Amanda
]
num_friends = len(friends)

# Start at Haight-Ashbury (location 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the Optimize instance.
opt = Optimize()

# Decision variables:
# x[i]: Boolean deciding whether to meet friend i.
# A[i]: Arrival time (in minutes) at friend i's location.
# order[i]: The meeting order if friend i is met; if not met, we force order[i] = -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if meeting is chosen then order[i] is between 0 and num_friends-1, else it is -1.
for i in range(num_friends):
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# If two friends are both chosen, they must have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability and minimum duration constraints:
# If friend i is met, let effective_start = max(A[i], available_start).
# Then effective_start + meeting_duration must be <= available_end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + meet_min <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), arrival time must be >= start_time + travel time from starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j follows friend i:
# then the arrival time at friend j must be >= departure time from friend i plus travel time.
# Departure time from i = max(A[i], avail_start of friend i) + meeting duration.
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

# Objective: Maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    chosen.sort()  # sort by meeting order

    print("Optimal meeting schedule:")
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    # Map friend indices to names and locations to names.
    friend_names = ["Elizabeth", "David", "Sandra", "Thomas", "Robert", "Kenneth", "Melissa", "Kimberly", "Amanda"]
    loc_names = {
        0: "Haight-Ashbury",
        1: "Mission District",
        2: "Union Square",
        3: "Pacific Heights",
        4: "Bayview",
        5: "Fisherman's Wharf",
        6: "Marina District",
        7: "Richmond District",
        8: "Sunset District",
        9: "Golden Gate Park"
    }
    
    for ord_val, i in chosen:
        loc, avail_start, avail_end, meet_min = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + meet_min
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc_names[loc]}")
        print(f"   Arrival time: {to_time(arrival)}")
        print(f"   Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")