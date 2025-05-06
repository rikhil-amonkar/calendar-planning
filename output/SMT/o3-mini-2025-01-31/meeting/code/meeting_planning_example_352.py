from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Union Square, Nob Hill, Haight-Ashbury, Chinatown, Marina District.
travel = {
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Marina District"): 18,
    
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Marina District"): 11,
    
    ("Haight-Ashbury", "Union Square"): 17,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,
    
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Chinatown"): 16,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is modeled as a tuple: (location, avail_start, avail_end, min_duration)
# Times are measured in minutes after midnight.
# We start at Union Square at 9:00AM (540 minutes).
#
# Karen: Nob Hill, 9:15PM to 9:45PM => 1275 to 1305, min duration = 30 minutes.
# Joseph: Haight-Ashbury, 12:30PM to 7:45PM => 750 to 1185, min duration = 90 minutes.
# Sandra: Chinatown, 7:15AM to 7:15PM => 435 to 1155, min duration = 75 minutes.
# Nancy: Marina District, 11:00AM to 8:15PM => 660 to 1215, min duration = 105 minutes.
friends = [
    ("Nob Hill", 1275, 1305, 30),     # Karen
    ("Haight-Ashbury", 750, 1185, 90),  # Joseph
    ("Chinatown", 435, 1155, 75),       # Sandra
    ("Marina District", 660, 1215, 105) # Nancy
]
friend_names = ["Karen", "Joseph", "Sandra", "Nancy"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Union Square"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean that is True if we decide to schedule a meeting with friend i.
# A[i] is an integer representing the arrival time (in minutes after midnight) at friend i's location.
# order[i] is an integer representing the sequence order in our visit (if scheduled, order is in 0 .. num_friends-1; if not, it is forced to -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if the meeting is scheduled then assign an order in the valid range; else force order to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Arrival times must be non-negative.
    opt.add(A[i] >= 0)

# Ensure no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, add the constraint for the meeting time window.
# The meeting can only start at the later of your arrival time A[i] or the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, minimal_duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + minimal_duration <= avail_end))

# For the first scheduled meeting (order == 0), ensure we can travel from the starting location (Union Square) in time.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # Get travel time from Union Square to the friend's location.
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings, ensure travel time between locations is respected.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, duration_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        # Meeting i starts at or after max(A[i], avail_start_i) and lasts for duration_i minutes.
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + duration_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with their corresponding order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
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