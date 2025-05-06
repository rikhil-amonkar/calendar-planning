from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# -------------------------------
# Travel times (in minutes) between locations.
# Format: (From, To): travel_time
travel = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,

    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,

    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,

    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,

    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,

    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# -------------------------------
# Friends data.
# Each friend is represented as a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times in minutes after midnight.
# Available times and meeting minimum durations are as follows:
#
# Stephanie : Mission District,  available 8:15AM (495) to 1:45PM (825), meeting >= 90 minutes.
# Sandra    : Bayview,         available 1:00PM (780) to 7:30PM (1170), meeting >= 15 minutes.
# Richard   : Pacific Heights, available 7:15AM (435) to 10:15AM (615), meeting >= 75 minutes.
# Brian     : Russian Hill,    available 12:15PM (735) to 4:00PM (960), meeting >= 120 minutes.
# Jason     : Fisherman's Wharf, available 8:30AM (510) to 5:45PM (1050), meeting >= 60 minutes.
friends = [
    ("Mission District",   495, 825, 90),   # Stephanie
    ("Bayview",            780, 1170, 15),  # Sandra
    ("Pacific Heights",    435, 615, 75),   # Richard
    ("Russian Hill",       735, 960, 120),  # Brian
    ("Fisherman's Wharf",  510, 1050, 60)   # Jason
]
friend_names = ["Stephanie", "Sandra", "Richard", "Brian", "Jason"]
num_friends = len(friends)

# -------------------------------
# Starting location and time.
start_loc = "Haight-Ashbury"
start_time = 540  # 9:00 AM

# -------------------------------
# Create the Z3 optimizer
opt = Optimize()

# Decision variables for each friend i:
#   x[i]: Bool, whether friend i is scheduled for a meeting.
#   A[i]: Int, arrival time (in minutes after midnight) to friend i's location.
#   order[i]: Int, the meeting order if scheduled; if not scheduled, we fix order = -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend scheduled, enforce order to be in [0, num_friends-1]; if not scheduled, order = -1.
for i in range(num_friends):
    opt.add( If(x[i],
                And(order[i] >= 0, order[i] < num_friends),
                order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add( Or(Not(x[i]), Not(x[j]), order[i] != order[j]) )

# For each friend, if scheduled, ensure the meeting fits within the available time.
# The meeting will start at the later of the arrival time A[i] and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # Meeting must finish by avail_end.
    opt.add( Or(Not(x[i]), meeting_start + min_dur <= avail_end) )

# Constraint for the first scheduled meeting:
# For any friend i that is scheduled with order 0,
# the arrival time A[i] must be at least start_time plus travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add( Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time) )

# Constraint for consecutive meetings:
# For any two meetings i and j where j follows i (order[j] == order[i] + 1),
# the arrival time at j must be at least the departure time from meeting i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        t_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add( Or(Not(cond), A[j] >= departure_i + t_time) )

# Objective: maximize total number of meetings scheduled.
opt.maximize( Sum([If(x[i], 1, 0) for i in range(num_friends)]) )

# -------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by order
    def to_time(minutes):
        hr = minutes // 60
        mn = minutes % 60
        return f"{hr:02d}:{mn:02d}"
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        start_meet = arrival if arrival >= avail_start else avail_start
        end_meet = start_meet + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival: {to_time(arrival)}")
        print(f"    Meeting: {to_time(start_meet)} to {to_time(end_meet)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")