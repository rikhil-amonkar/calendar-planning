from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define the locations:
locations = [
    "Nob Hill",
    "Richmond District",
    "Financial District",
    "North Beach",
    "The Castro",
    "Golden Gate Park"
]

# Travel times dictionary (directional):
travel = {
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,

    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,

    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,

    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,

    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13
}

# Define friend meeting information.
# Each friend is represented as a tuple: 
# (location, avail_start, avail_end, min_duration), with times in minutes after midnight.
friends = [
    # Emily: Richmond District, 7:00PM to 9:00PM, minimum 15 minutes.
    ("Richmond District", 1140, 1260, 15),
    # Margaret: Financial District, 4:30PM to 8:15PM, minimum 75 minutes.
    ("Financial District", 990, 1215, 75),
    # Ronald: North Beach, 6:30PM to 7:30PM, minimum 45 minutes.
    ("North Beach", 1110, 1170, 45),
    # Deborah: The Castro, 1:45PM to 9:15PM, minimum 90 minutes.
    ("The Castro", 825, 1275, 90),
    # Jeffrey: Golden Gate Park, 11:15AM to 2:30PM, minimum 120 minutes.
    ("Golden Gate Park", 675, 870, 120)
]
num_friends = len(friends)

# Starting conditions:
# You arrive at Nob Hill at 9:00AM (540 minutes after midnight).
start_loc = "Nob Hill"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
#   x[i]: Boolean indicating if we schedule a meeting with friend i.
#   A[i]: Arrival time (in minutes) at friend i's location.
#   order[i]: Integer indicating the order of the meeting if scheduled (0 ... num_friends-1)
#             or -1 if not scheduled.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If meeting i is scheduled, then its order is between 0 and num_friends-1; otherwise, order is -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Enforce meeting availability for each friend.
# The meeting for friend i will actually begin at the later of your arrival time and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # The meeting must finish before or exactly at the available end.
    opt.add(Or(Not(x[i]), meeting_start + duration <= avail_end))

# Travel constraints:
# For the first scheduled meeting (order == 0): your arrival time must be at least the start time plus travel time
# from your start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if meeting j immediately follows meeting i, then your arrival time for meeting j
# must be at least (meeting start time at i + duration at i) plus the travel time from friend i’s location to j’s location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        depart_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= depart_i + t_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather the scheduled meetings along with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    def to_time(t):
        # Convert minutes to HH:MM (24-hour format)
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Emily", "Margaret", "Ronald", "Deborah", "Jeffrey"]
    for ord_val, i in schedule:
        loc, avail_start, avail_end, duration = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + duration
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")