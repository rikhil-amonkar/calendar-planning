from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at Bayview at 9:00AM (540 minutes).
friends = [
    # 0: Richard at Union Square: available from 8:45AM (525) to 1:00PM (780), meeting at least 120 mins.
    ("Union Square", 525, 780, 120),
    # 1: Charles at Presidio: available from 9:45AM (585) to 1:00PM (780), meeting at least 120 mins.
    ("Presidio", 585, 780, 120),
]
friend_names = ["Richard", "Charles"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Bayview"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Bool variable that is True if meeting friend i is scheduled.
# A[i]: Integer variable representing the arrival time at friend i's location.
# order[i]: Integer variable representing order in which friend i is visited.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a friend is scheduled then order must be between 0 and num_friends-1; else we fix order to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For a scheduled meeting, the meeting starts at the later of your arrival and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location (Bayview).
# If friend i is scheduled first (order[i]==0), ensure your arrival time A[i] is no earlier than:
# start_time + (travel time from Bayview to friend i's location)
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# (Here, if two meetings were scheduled, we would need to ensure enough travel time between them.)
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"
    
    print("Optimal meeting schedule:")
    for i in range(num_friends):
        if model.evaluate(x[i]):
            loc, avail_start, avail_end, dur = friends[i]
            arrival = model.evaluate(A[i]).as_long()
            start_meeting = arrival if arrival >= avail_start else avail_start
            meeting_end = start_meeting + dur
            print(f"Meet {friend_names[i]} at {loc}")
            print(f"  Arrival Time: {to_time(arrival)}")
            print(f"  Meeting Time: {to_time(start_meeting)} - {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")