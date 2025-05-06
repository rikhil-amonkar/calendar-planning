from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Russian Hill, Presidio, Chinatown, Pacific Heights, Richmond District, 
# Fisherman's Wharf, Golden Gate Park, Bayview.
travel = {
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,

    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,

    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,

    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,

    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 26,

    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,

    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,

    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend: (location, avail_start, avail_end, min_duration)
# Times are given in minutes after midnight.
friends = [
    # Matthew at Presidio: 11:00AM (660) to 9:00PM (1260), minimum 90 minutes.
    ("Presidio", 660, 1260, 90),
    # Margaret at Chinatown: 9:15AM (555) to 6:45PM (1125), minimum 90 minutes.
    ("Chinatown", 555, 1125, 90),
    # Nancy at Pacific Heights: 2:15PM (855) to 5:00PM (1020), minimum 15 minutes.
    ("Pacific Heights", 855, 1020, 15),
    # Helen at Richmond District: 7:45PM (1185) to 10:00PM (1320), minimum 60 minutes.
    ("Richmond District", 1185, 1320, 60),
    # Rebecca at Fisherman's Wharf: 9:15PM (1275) to 10:15PM (1335), minimum 60 minutes.
    ("Fisherman's Wharf", 1275, 1335, 60),
    # Kimberly at Golden Gate Park: 1:00PM (780) to 4:30PM (990), minimum 120 minutes.
    ("Golden Gate Park", 780, 990, 120),
    # Kenneth at Bayview: 2:30PM (870) to 6:00PM (1080), minimum 60 minutes.
    ("Bayview", 870, 1080, 60),
]
friend_names = ["Matthew", "Margaret", "Nancy", "Helen", "Rebecca", "Kimberly", "Kenneth"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
# You arrive at Russian Hill at 9:00AM (540 minutes after midnight)
start_loc = "Russian Hill"
start_time = 540

# ----------------------------------------------------------------------------
# Create the optimizer
opt = Optimize()

# Decision variables:
# x[i]    : Boolean indicating if meeting with friend i is scheduled.
# A[i]    : Arrival time (in minutes after midnight) at friend i's location.
# order[i]: Integer representing the sequence order if scheduled (0 to num_friends-1) or -1 otherwise.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if the meeting is scheduled then order[i] must be between 0 and num_friends-1,
# otherwise, order[i] is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order numbers for scheduled meetings
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, the meeting must start no earlier than the later of your arrival A[i]
# or the friend’s available start, last for the minimum duration, and finish by the available end time.
for i in range(num_friends):
    loc, avail_start, avail_end, duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + duration <= avail_end))

# For the first scheduled meeting (order == 0), ensure sufficient travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings: if friend j comes immediately after friend i,
# ensure that travel time from friend i's location to friend j's location is respected.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, duration_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + duration_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with their order.
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