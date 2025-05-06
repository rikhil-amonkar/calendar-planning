from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Locations: Nob Hill, Pacific Heights, Mission District.
travel = {
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Mission District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each tuple: (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight.
# You arrive at Nob Hill at 9:00AM (540 minutes).
friends = [
    # Thomas at Pacific Heights: 3:30PM (930) to 7:15PM (1155), minimum duration 75 minutes.
    ("Pacific Heights", 930, 1155, 75),
    # Kenneth at Mission District: 12:00PM (720) to 3:45PM (945), minimum duration 45 minutes.
    ("Mission District", 720, 945, 45),
]
friend_names = ["Thomas", "Kenneth"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Nob Hill"
start_time = 540  # 9:00 AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean variable indicating if meeting friend i is scheduled.
# A[i]: Arrival time (in minutes after midnight) at friend i's location.
# order[i]: Integer variable representing the order in which friend i is visited.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Ensure that if a meeting is scheduled, its order is in range 0..num_friends-1; otherwise, set to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Arrival times must be non-negative.
    opt.add(A[i] >= 0)

# No two scheduled meetings should share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints for each friend.
# The meeting begins at the later of your arrival time and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # If scheduled, the meeting (which lasts min_dur) must finish by avail_end.
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location (Nob Hill) for the first scheduled meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    # If friend i is the first meeting (order == 0), then arrival time A[i] must be
    # at least start_time + travel_time.
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        # If friend j is visited right after friend i, account for travel time.
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: Maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the problem and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Order scheduled meetings by their assigned order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    def to_time(t):
        hr = t // 60
        mn = t % 60
        return f"{hr:02d}:{mn:02d}"

    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
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