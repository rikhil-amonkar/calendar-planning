from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: North Beach, Mission District, The Castro.
travel = {
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at North Beach at 9:00AM (540 minutes).
friends = [
    # James at Mission District: available 12:45PM (765) to 2:00PM (840), min 75 minutes.
    ("Mission District", 765, 840, 75),
    # Robert at The Castro: available 12:45PM (765) to 3:15PM (915), min 30 minutes.
    ("The Castro", 765, 915, 30),
]
friend_names = ["James", "Robert"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "North Beach"
start_time = 540  # 9:00 AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create a Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean variable: True if meeting friend i is scheduled.
# A[i]: Arrival time (in minutes after midnight) at the meeting location for friend i.
# order[i]: Integer variable representing the order in which friend i is visited (if scheduled, value in 0..num_friends-1; if not, -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if the meeting is scheduled, then order must be in range 0..num_friends-1; else order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Ensure arrival time is non-negative.
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting window constraints for each friend.
# The meeting starts at the later of A[i] and the friend’s available start time.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # If meeting i is scheduled, then meeting_end must be <= avail_end.
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint from starting location (North Beach) for the first scheduled meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    # If friend i is the first meeting in the schedule (order==0) then A[i] must be at least start_time + travel_time.
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

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
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Extract scheduled meetings and order them.
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
        # The meeting begins at the later of arrival and available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")