from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define location indices:
# 0: Financial District
# 1: Russian Hill
# 2: Sunset District
# 3: North Beach
# 4: The Castro
# 5: Golden Gate Park

# Travel distances (in minutes) between locations.
# Provided as (from, to): travel time.
travel = {
    # From Financial District (0)
    (0,1): 10, (0,2): 31, (0,3): 7,  (0,4): 23, (0,5): 23,
    # From Russian Hill (1)
    (1,0): 11, (1,2): 23, (1,3): 5,  (1,4): 21, (1,5): 21,
    # From Sunset District (2)
    (2,0): 30, (2,1): 24, (2,3): 29, (2,4): 17, (2,5): 11,
    # From North Beach (3)
    (3,0): 8,  (3,1): 4,  (3,2): 27, (3,4): 22, (3,5): 22,
    # From The Castro (4)
    (4,0): 20, (4,1): 18, (4,2): 17, (4,3): 20, (4,5): 11,
    # From Golden Gate Park (5)
    (5,0): 26, (5,1): 19, (5,2): 10, (5,3): 24, (5,4): 13
}

# Friends meeting information.
# Each friend is represented as a tuple:
#   (location, available_start, available_end, minimum_meeting_duration)
#
# Times are in minutes after midnight.
#
# Ronald     at Russian Hill (loc 1):       1:45PM to 5:15PM  ==>  825 to 1035, min 105 minutes.
# Patricia   at Sunset District (loc 2):      9:15AM to 10:00PM  ==> 555 to 1320, min 60 minutes.
# Laura      at North Beach (loc 3):          12:30PM to 12:45PM  ==> 750 to 765, min 15 minutes.
# Emily      at The Castro (loc 4):           4:15PM to 6:30PM   ==> 975 to 1110, min 60 minutes.
# Mary       at Golden Gate Park (loc 5):       3:00PM to 4:30PM   ==> 900 to 990, min 60 minutes.
friends = [
    (1, 825, 1035, 105),  # Ronald
    (2, 555, 1320, 60),   # Patricia
    (3, 750, 765, 15),    # Laura
    (4, 975, 1110, 60),   # Emily
    (5, 900, 990, 60)     # Mary
]
num_friends = len(friends)

# Starting point: Financial District (0) at 9:00AM (540 minutes).
start_loc = 0
start_time = 540

# Initialize the solver as an Optimize instance.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i] is True if you choose to meet friend i.
#   A[i] is the arrival time (in minutes) at friend i's meeting location.
#   order[i] is the order of the meeting if scheduled; if not scheduled, we force order[i] = -1.
x = [ Bool(f"x_{i}") for i in range(num_friends) ]
A = [ Int(f"A_{i}") for i in range(num_friends) ]
order = [ Int(f"order_{i}") for i in range(num_friends) ]

# If a friend is chosen, set order in the range [0, num_friends-1].
# If not chosen, force order[i] to be -1.
for i in range(num_friends):
    opt.add( If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1) )
    opt.add( A[i] >= 0 )

# Ensure that if two friends are both scheduled, they must have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add( Or(Not(x[i]), Not(x[j]), order[i] != order[j]) )

# Meeting availability and duration constraints:
# If friend i is met, the effective meeting start is max(arrival time, available start).
# Then, effective meeting start + meeting duration must be <= available end.
for i in range(num_friends):
    loc, avail_start, avail_end, meet_min = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add( Or( Not(x[i]), effective_start + meet_min <= avail_end ) )

# Add travel constraints:
# For the first meeting in the itinerary (order == 0), ensure there is enough time
# to travel from the starting location (Financial District) to the friend's location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add( Or( Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time) )

# For consecutive meetings, if friend j is scheduled immediately after friend i,
# then the arrival time at j must be at least the departure time from i plus travel time.
# Here, we define departure time from friend i as (max(A[i], avail_start of i) + meeting duration).
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, meet_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + meet_i
        travel_time = travel[(loc_i, loc_j)]
        # If friend j is scheduled immediately after friend i, add the constraint.
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add( Or(Not(cond), A[j] >= departure_i + travel_time) )

# Objective: Maximize the number of friends met.
opt.maximize( Sum([If(x[i], 1, 0) for i in range(num_friends)]) )

# Check for satisfiability and then output an optimal schedule.
if opt.check() == sat:
    model = opt.model()
    chosen = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            chosen.append((model.evaluate(order[i]).as_long(), i))
    # Sort meetings by their order.
    chosen.sort()
    
    print("Optimal meeting schedule:")
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    loc_names = {
        0: "Financial District",
        1: "Russian Hill",
        2: "Sunset District",
        3: "North Beach",
        4: "The Castro",
        5: "Golden Gate Park"
    }
    friend_names = ["Ronald", "Patricia", "Laura", "Emily", "Mary"]
    
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