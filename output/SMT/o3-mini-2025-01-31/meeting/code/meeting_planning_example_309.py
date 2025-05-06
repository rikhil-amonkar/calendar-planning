from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Financial District, Chinatown, Alamo Square, Bayview, Fisherman's Wharf.
travel = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,

    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Fisherman's Wharf"): 8,

    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,

    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,

    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Bayview"): 26,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Nancy:   at Chinatown, available 9:30AM (570) to 1:30PM (810), min_duration = 90.
# Mary:    at Alamo Square, available 7:00AM (420) to 9:00PM (1260), min_duration = 75.
# Jessica: at Bayview, available 11:15AM (675) to 1:45PM (825), min_duration = 45.
# Rebecca: at Fisherman's Wharf, available 7:00AM (420) to 8:30AM (510), min_duration = 45.
friends = [
    ("Chinatown",       570, 810, 90),   # Nancy
    ("Alamo Square",    420, 1260, 75),  # Mary
    ("Bayview",         675, 825, 45),   # Jessica
    ("Fisherman's Wharf",420, 510, 45),   # Rebecca
]
friend_names = ["Nancy", "Mary", "Jessica", "Rebecca"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Financial District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean indicating if meeting with friend i is scheduled.
# A[i]: Integer representing your arrival time at friend i’s location.
# order[i]: Integer representing the visitation order (0..num_friends-1), or -1 if not scheduled.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting is scheduled, order[i] is between 0 and (num_friends-1). Otherwise, order[i] = -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order numbers for scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, meeting start is the later of arrival time A[i] and avail_start.
# The meeting must last for the min_duration and finish by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure enough travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    tt = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + tt))

# For consecutive scheduled meetings:
# If friend j immediately follows friend i, then your arrival at j must be at least the departure time of i
# (meeting_start + duration) plus travel time from friend i's location to friend j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_ij))

# ----------------------------------------------------------------------------
# Objective: Maximize number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings and sort them by their order.
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