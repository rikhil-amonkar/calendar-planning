from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Locations: Fisherman's Wharf, Nob Hill.
travel = {
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 11
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Starting at Fisherman's Wharf at 9:00AM (540 minutes).
#
# Kenneth: at Nob Hill from 2:15PM to 7:45PM => [855, 1185], min_duration = 90.
friends = [
    ("Nob Hill", 855, 1185, 90)  # Kenneth
]
friend_names = ["Kenneth"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Start parameters.
start_loc = "Fisherman's Wharf"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create Z3 optimizer.
opt = Optimize()

# Decision Variables:
# x[i]: Bool, True if meeting with friend i is scheduled.
# A[i]: Int, arrival time at friend i's location.
# order[i]: Int, visitation order if meeting is scheduled (order in [0, num_friends-1]); if not scheduled then -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if meeting is scheduled then assign an order in [0, num_friends-1] otherwise fix order[i] to -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings (if more than one) have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, ensure the meeting fits within the friend's available window.
# The meeting starts at the later of arrival time and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# Constraint: For the first scheduled meeting, ensure enough travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings sorted by their order.
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