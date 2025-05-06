from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define the locations.
locations = [
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Presidio",
    "Richmond District"
]

# Travel times (in minutes, directional)
travel = {
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7
}

# Define friend meeting information.
# Each friend is defined by a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times in minutes after midnight.
friends = [
    # Melissa: Golden Gate Park, available from 8:30AM (510) to 8:00PM (1200), min 15 minutes.
    ("Golden Gate Park", 510, 1200, 15),
    # Nancy: Presidio, available from 7:45PM (1185) to 10:00PM (1320), min 105 minutes.
    ("Presidio", 1185, 1320, 105),
    # Emily: Richmond District, available from 4:45PM (1005) to 10:00PM (1320), min 120 minutes.
    ("Richmond District", 1005, 1320, 120)
]
num_friends = len(friends)

# Starting conditions:
# You arrive at Fisherman's Wharf at 9:00AM, i.e. 540 minutes.
start_loc = "Fisherman's Wharf"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
#   x[i]: Boolean, True if meeting with friend i is scheduled.
#   A[i]: Integer, representing the arrival time (in minutes) at that friend's location.
#   order[i]: Integer, representing the meeting order if scheduled (0, 1, ...), else -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If meeting is scheduled, its order is between 0 and num_friends-1; if not, order is -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Enforce meeting availability for each friend.
# Meeting begins at max(arrival time, availability start) and lasts for the minimum duration.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint from starting point:
# For the first scheduled meeting (order 0), you must travel from Fisherman's Wharf.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraint between consecutive scheduled meetings:
# If meeting j immediately follows meeting i, then arrival time at j must be at least
# (max(A[i], avail_start_i) + min_dur_i) + travel_time(i -> j)
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        depart_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= depart_i + t_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Check and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Melissa", "Nancy", "Emily"]
    for ord_val, i in schedule:
        loc, avail_start, avail_end, min_dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting actually begins when you arrive and when the friend is available.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + min_dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")