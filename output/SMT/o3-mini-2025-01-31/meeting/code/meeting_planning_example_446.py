from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define location indices:
# 0: Richmond District
# 1: Marina District
# 2: Chinatown
# 3: Financial District
# 4: Bayview
# 5: Union Square

# Travel distances in minutes between locations:
# Provided distances (from X to Y)
travel = {
    # From Richmond District (0)
    (0,1): 9, (0,2): 20, (0,3): 22, (0,4): 26, (0,5): 21,
    # From Marina District (1)
    (1,0): 11, (1,2): 16, (1,3): 17, (1,4): 27, (1,5): 16,
    # From Chinatown (2)
    (2,0): 20, (2,1): 12, (2,3): 5,  (2,4): 22, (2,5): 7,
    # From Financial District (3)
    (3,0): 21, (3,1): 15, (3,2): 5,  (3,4): 19, (3,5): 9,
    # From Bayview (4)
    (4,0): 25, (4,1): 25, (4,2): 18, (4,3): 19, (4,5): 17,
    # From Union Square (5)
    (5,0): 20, (5,1): 18, (5,2): 7,  (5,3): 9,  (5,4): 15
}

# Friend meeting information:
# Each friend is defined as (location, avail_start, avail_end, meeting_min)
# Times in minutes after midnight.
# Kimberly: Marina District (1)  from 1:15PM (795) to 4:45PM (1005), min 15.
# Robert:   Chinatown (2)       from 12:15PM (735) to 8:15PM (1215), min 15.
# Rebecca:  Financial District (3) from 1:15PM (795) to 4:45PM (1005), min 75.
# Margaret: Bayview (4)         from 9:30AM (570)  to 1:30PM (810), min 30.
# Kenneth:  Union Square (5)     from 7:30PM (1170) to 9:15PM (1275), min 75.
friends = [
    (1, 795, 1005, 15),   # Kimberly
    (2, 735, 1215, 15),   # Robert
    (3, 795, 1005, 75),   # Rebecca
    (4, 570, 810, 30),    # Margaret
    (5, 1170, 1275, 75)   # Kenneth
]
num_friends = len(friends)

# Start at Richmond District (location 0) at 9:00AM (540 minutes)
start_loc = 0
start_time = 540

# Initialize the optimizer.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i]: True if meeting friend i.
#   A[i]: Arrival time at friend's location.
#   order[i]: The position (order) in the itinerary if friend is met; if not, we set it to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if chosen, order should be in 0 ... num_friends-1; if not, we set order to -1.
for i in range(num_friends):
    # If friend is chosen, order in range, else order equals -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    # Arrival times must be nonnegative.
    opt.add(A[i] >= 0)

# If more than one friend is chosen, their order numbers must be distinct.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting window constraints:
# For each friend i, the effective meeting start is max(arrival, avail_start).
# Then meeting end = effective start + meeting duration must be <= avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + meet_min <= avail_end))

# Travel constraints:
# For the first meeting (order==0), require travel from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j comes immediately after friend i,
# then the arrival time at friend j must be at least the departure time from friend i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j: 
            continue
        loc_i, avail_i, _, meet_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        # Departure time from friend i is effective meeting start plus meeting duration.
        dep_i = If(A[i] < avail_i, avail_i, A[i]) + meet_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= dep_i + travel_time))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Check and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    chosen.sort()  # sort by itinerary order
    print("Optimal meeting schedule:")
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    # Map location indices to names.
    loc_names = {
        0: "Richmond District",
        1: "Marina District",
        2: "Chinatown",
        3: "Financial District",
        4: "Bayview",
        5: "Union Square"
    }
    friend_names = ["Kimberly", "Robert", "Rebecca", "Margaret", "Kenneth"]
    
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