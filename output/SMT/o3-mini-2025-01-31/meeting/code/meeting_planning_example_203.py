from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define the locations.
locations = [
    "Financial District",
    "Fisherman's Wharf",
    "Pacific Heights",
    "Mission District"
]

# Travel times in minutes (directional):
# For example: from Financial District to Fisherman's Wharf takes 10 minutes.
travel = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Pacific Heights"): 16
}

# Define friend meeting information.
# Each friend is represented as (location, avail_start, avail_end, min_duration)
# Times are given in minutes after midnight.
friends = [
    # David at Fisherman's Wharf: 10:45 AM to 3:30 PM, minimum meeting duration 15 minutes.
    ("Fisherman's Wharf", 645, 930, 15),
    # Timothy at Pacific Heights: 9:00 AM to 3:30 PM, minimum meeting duration 75 minutes.
    ("Pacific Heights", 540, 930, 75),
    # Robert at Mission District: 12:15 PM to 7:45 PM, minimum meeting duration 90 minutes.
    ("Mission District", 735, 1185, 90)
]
num_friends = len(friends)

# Starting conditions:
# You arrive at the Financial District at 9:00 AM = 540 minutes.
start_loc = "Financial District"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Create decision variables for each friend i:
#   x[i]: Boolean indicating whether to schedule meeting with friend i.
#   A[i]: Integer representing arrival time (in minutes) at friend i's location.
#   order[i]: Integer indicating the order of the meeting (0 to num_friends-1) if scheduled, and -1 otherwise.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If scheduled, order is between 0 and num_friends-1; if not, order is -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    # Arrival time must be non-negative.
    opt.add(A[i] >= 0)

# Ensure scheduled meetings have unique order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i, meeting start is the later of your arrival time A[i] and their availability start.
# The meeting must finish (start time + min_duration) before the availability end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints from starting location:
# For the first scheduled meeting (order == 0), you must travel from the Financial District.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))
    
# Travel constraints between consecutive scheduled meetings:
# If friend j is scheduled immediately after friend i, then you leave friend i at:
#   departure_i = max(A[i], avail_start_i) + min_dur_i and arrive at friend j after travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# Objective: maximize the number of meetings (friends met).
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings sorted by order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    def to_time(t):
        # Convert minutes after midnight to HH:MM format.
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["David", "Timothy", "Robert"]
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The scheduled meeting begins when both you arrive and the friend is available.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")