from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Locations: North Beach, Pacific Heights, Chinatown, Union Square, Mission District, Golden Gate Park, Nob Hill.
travel = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,

    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,

    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 8,

    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Nob Hill"): 9,

    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,

    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Nob Hill"): 20,

    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Times are minutes after midnight.
# James: at Pacific Heights from 8:00PM to 10:00PM (1200 to 1320) - min meeting duration: 120 minutes.
# Robert: at Chinatown from 12:15PM to 4:45PM (735 to 1005) - min meeting duration: 90 minutes.
# Jeffrey: at Union Square from 9:30AM to 3:30PM (570 to 930) - min meeting duration: 120 minutes.
# Carol: at Mission District from 6:15PM to 9:15PM (1095 to 1275) - min meeting duration: 15 minutes.
# Mark: at Golden Gate Park from 11:30AM to 5:45PM (690 to 1065) - min meeting duration: 15 minutes.
# Sandra: at Nob Hill from 8:00AM to 3:30PM (480 to 930) - min meeting duration: 15 minutes.
friends = [
    ("Pacific Heights", 1200, 1320, 120),  # James
    ("Chinatown",       735, 1005, 90),      # Robert
    ("Union Square",    570, 930, 120),       # Jeffrey
    ("Mission District",1095, 1275, 15),      # Carol
    ("Golden Gate Park",690, 1065, 15),       # Mark
    ("Nob Hill",        480, 930, 15),        # Sandra
]
friend_names = ["James", "Robert", "Jeffrey", "Carol", "Mark", "Sandra"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "North Beach"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]: Bool - True if meeting with friend i is scheduled.
#   A[i]: Int  - Arrival time (in minutes after midnight) at friend i's location.
#   order[i]: Int - The order in which friend i is visited (if scheduled, in [0, num_friends-1]; if not, fixed to -1).
x     = [Bool(f"x_{i}") for i in range(num_friends)]
A     = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a friend is scheduled then order in [0, num_friends-1] is assigned; otherwise order is fixed to -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i that is scheduled, ensure the meeting fits within the time window.
# The meeting actually starts at the later of your arrival time A[i] and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), enforce travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings:
# If friend j is visited immediately after friend i then the arrival time at j must be at least the departure time from i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# --------------------------------------------------------------------
# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()

    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    print("Optimal meeting schedule:")
    for ord_val, i in scheduled:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")