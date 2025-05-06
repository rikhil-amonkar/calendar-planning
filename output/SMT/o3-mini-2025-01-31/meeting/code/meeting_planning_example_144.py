from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Locations: The Castro, Mission District, Financial District.
travel = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Times are in minutes after midnight.
# Laura: at Mission District from 12:15PM to 7:45PM (735 to 1185) - minimum meeting 75 minutes.
# Anthony: at Financial District from 12:30PM to 2:45PM (750 to 885)  - minimum meeting 30 minutes.
friends = [
    ("Mission District", 735, 1185, 75),   # Laura
    ("Financial District", 750, 885, 30),    # Anthony
]
friend_names = ["Laura", "Anthony"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "The Castro"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]: Boolean variable indicating if meeting with friend i is scheduled.
#   A[i]: Integer variable representing the arrival time at friend i's location.
#   order[i]: Integer representing the order in which the friend is visited (if scheduled, in [0, num_friends-1]; otherwise fixed to -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then set order in [0, num_friends-1],
# otherwise fix the order to -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings have distinct orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, ensure the meeting fits within the available window.
# The meeting actually starts at the later of your arrival time A[i] and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # Meeting must finish by avail_end.
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), enforce travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings:
# If friend j is visited immediately after friend i then:
#    Arrival time at j must be at least departure time from i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        # Meeting at i starts at the later of A[i] or avail_start_i.
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# --------------------------------------------------------------------
# Objective: Maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()

    # Get scheduled friends sorted by order.
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()

    def to_time(minutes):
        hr = minutes // 60
        mn = minutes % 60
        return f"{hr:02d}:{mn:02d}"

    print("Optimal meeting schedule:")
    for ord_val, i in scheduled:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")