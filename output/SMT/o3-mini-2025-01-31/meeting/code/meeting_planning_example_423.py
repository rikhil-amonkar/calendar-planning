from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location indices:
# 0: Presidio (starting point)
# 1: Richmond District
# 2: North Beach
# 3: Financial District
# 4: Golden Gate Park
# 5: Union Square

# Travel distances (in minutes) between locations.
# (from, to) : travel_time
travel = {
    # From Presidio (0)
    (0,1): 7,  (0,2): 18, (0,3): 23, (0,4): 12, (0,5): 22,
    # From Richmond District (1)
    (1,0): 7,  (1,2): 17, (1,3): 22, (1,4): 9,  (1,5): 21,
    # From North Beach (2)
    (2,0): 17, (2,1): 18, (2,3): 8,  (2,4): 22, (2,5): 7,
    # From Financial District (3)
    (3,0): 22, (3,1): 21, (3,2): 7,  (3,4): 23, (3,5): 9,
    # From Golden Gate Park (4)
    (4,0): 11, (4,1): 7,  (4,2): 24, (4,3): 26, (4,5): 22,
    # From Union Square (5)
    (5,0): 24, (5,1): 20, (5,2): 10, (5,3): 9,  (5,4): 22
}

# Friend meeting information.
# Each tuple represents:
#   (location, available_start, available_end, minimum_meeting_duration)
# Times are in minutes after midnight.
#
# Jason:    at Richmond District (1):  from 1:00PM (780) to 8:45PM (1245), min 90 minutes.
# Melissa:  at North Beach (2):          from 6:45PM (1125) to 8:15PM (1155), min 45 minutes.
# Brian:    at Financial District (3):   from 9:45AM (585) to 9:45PM (1305), min 15 minutes.
# Elizabeth:at Golden Gate Park (4):     from 8:45AM (525) to 9:30PM (1290), min 105 minutes.
# Laura:    at Union Square (5):         from 2:15PM (855) to 7:30PM (1170), min 75 minutes.
friends = [
    (1, 780, 1245, 90),    # Jason
    (2, 1125, 1155, 45),   # Melissa
    (3, 585, 1305, 15),    # Brian
    (4, 525, 1290, 105),   # Elizabeth
    (5, 855, 1170, 75)     # Laura
]
num_friends = len(friends)

# Start at Presidio (location 0) at 9:00AM = 540 minutes.
start_loc = 0
start_time = 540

# Create the optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean to indicate if we choose to meet friend i.
# A[i]: Arrival time (in minutes) at friend i's location.
# order[i]: The order of the meeting if scheduled; if not scheduled, it is forced to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a friend is met, set order in the range 0 to num_friends-1; otherwise, force order = -1.
for i in range(num_friends):
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# If two friends are both chosen, they get distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# If friend i is met, then the effective meeting start time is:
#    effective_start = max(A[i], available_start).
# The meeting must finish by available_end; hence, effective_start + meeting_duration <= available_end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + meet_min <= avail_end))

# Travel constraints:
# For the first meeting (order == 0), ensure enough travel time from start (Presidio).
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j is scheduled immediately after friend i, then:
#    A[j] must be >= departure time from friend i + travel time from friend i's location to friend j's location.
# Define departure time from friend i as: max(A[i], available_start of friend i) + meeting duration.
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

# Check and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    chosen.sort()
    
    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Jason", "Melissa", "Brian", "Elizabeth", "Laura"]
    loc_names = {
        0: "Presidio",
        1: "Richmond District",
        2: "North Beach",
        3: "Financial District",
        4: "Golden Gate Park",
        5: "Union Square"
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