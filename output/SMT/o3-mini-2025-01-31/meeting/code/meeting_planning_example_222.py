from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Nob Hill, North Beach, Fisherman's Wharf, Bayview.
travel = {
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,

    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Bayview"): 22,

    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Bayview"): 26,

    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Fisherman's Wharf"): 25,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Helen:      at North Beach,         available 7:00AM (420) to 4:45PM (16:45 -> 1005),   min_duration = 120.
# Kimberly:   at Fisherman's Wharf,   available 4:30PM (990) to 9:00PM (1260),                min_duration = 45.
# Patricia:   at Bayview,             available 6:00PM (1080) to 9:15PM (1275),               min_duration = 120.
friends = [
    ("North Beach",       420, 1005, 120),   # Helen
    ("Fisherman's Wharf", 990, 1260, 45),    # Kimberly
    ("Bayview",           1080, 1275, 120),  # Patricia
]
friend_names = ["Helen", "Kimberly", "Patricia"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
# You arrive at Nob Hill at 9:00AM (540 minutes after midnight)
start_loc = "Nob Hill"
start_time = 540

# ----------------------------------------------------------------------------
# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# x[i]: Boolean - whether meeting with friend i is scheduled.
# A[i]: Integer - arrival time at friend i's location.
# order[i]: Integer - position in sequence (if scheduled then 0 <= order[i] < num_friends, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Set order variables: if meeting is scheduled, order must be 0 .. num_friends-1, else must be -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that if two meetings are scheduled, their orders are distinct.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled then the meeting must start no earlier than the later of your arrival (A[i])
# or the friend's available start time, last the minimum duration, and finish by available end time.
for i in range(num_friends):
    loc, avail_start, avail_end, duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + duration <= avail_end))

# For the first scheduled meeting (order == 0), make sure you have enough travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # Look up travel time from start_loc to friend's location
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings: if friend j is immediately after friend i, ensure enough travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i  # finish time at friend i's meeting
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Create a list of scheduled meetings (order, friend index)
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
        loc, avail_start, avail_end, duration = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + duration
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")