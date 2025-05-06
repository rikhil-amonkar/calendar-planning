from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define the meeting locations for the friends.
# Also define the friends as tuples: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Emily: located at Union Square, available from 4:00PM (960) to 5:15PM (1035); min meeting = 45 minutes.
    ("Union Square", 960, 1035, 45),
    # Margaret: located at Russian Hill, available from 7:00PM (1140) to 9:00PM (1260); min meeting = 120 minutes.
    ("Russian Hill", 1140, 1260, 120)
]
num_friends = len(friends)

# Starting condition:
# You arrive at North Beach at 9:00AM = 540 minutes.
start_loc = "North Beach"
start_time = 540

# Define directional travel times (in minutes) between neighborhoods.
# Only required pairs between: North Beach, Union Square, Russian Hill.
travel = {
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Russian Hill"): 13,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11
}

# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend:
# x[i] is a Bool that is True if we schedule a meeting with friend i.
# A[i] is an Int for the arrival time (in minutes) at the friend’s location.
# order[i] is an Int representing the order in which the meeting is held; if not scheduled it is -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If scheduled, order is between 0 and num_friends-1; if not scheduled, order is -1.
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Arrival time is non-negative.
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have unique order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, enforce the meeting window constraint.
# Meeting starts at max(arrival time, avail_start) and lasts for at least the minimum duration before avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints from the starting location.
# For the first meeting (order == 0), the arrival time must be at least start_time + travel time from start_loc.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings.
# If friend j follows friend i (order[j] == order[i] + 1), then the arrival time at j must be:
# departure from i plus travel time from friend i's location to friend j's location.
# Departure time from friend i is defined as max(A[i], avail_start_i) + min_duration_i.
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

# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect the scheduled meetings along with their order.
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
    
    friend_names = ["Emily", "Margaret"]
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting cannot start before the friend is available.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")