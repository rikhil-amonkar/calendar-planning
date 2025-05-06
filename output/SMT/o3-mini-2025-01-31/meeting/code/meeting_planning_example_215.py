from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From Bayview
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    
    # From Embarcadero
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    
    # From Richmond District
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Richmond District"): 18
}

# Define friend meeting details.
# Each friend is represented as (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Jessica: at Embarcadero from 4:45PM (1005) to 7:00PM (1140), meeting >= 30 minutes.
    ("Embarcadero", 1005, 1140, 30),
    # Sandra: at Richmond District from 6:30PM (1110) to 9:45PM (1305), meeting >= 120 minutes.
    ("Richmond District", 1110, 1305, 120),
    # Jason: at Fisherman's Wharf from 4:00PM (960) to 4:45PM (1005), meeting >= 30 minutes.
    ("Fisherman's Wharf", 960, 1005, 30)
]
friend_names = ["Jessica", "Sandra", "Jason"]
num_friends = len(friends)

# Starting conditions: You arrive at Bayview at 9:00AM = 540 minutes after midnight.
start_loc = "Bayview"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
# x[i]: Bool indicator if meeting is scheduled.
# A[i]: Int for arrival time at friend's location.
# order[i]: Int for meeting order (if scheduled, in [0, num_friends-1], else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting is scheduled then order[i] is between 0 and num_friends-1; otherwise, force it to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Enforce that scheduled meetings have distinct order indices.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# For each friend, if the meeting is scheduled, then the meeting starts at the later of arrival A[i] or avail_start.
# The meeting (start + min_duration) must end by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any friend i, if it is the first meeting (order[i] == 0), then your arrival time must be at least start_time + travel time from Bayview.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraint between consecutive meetings:
# For any two scheduled meetings i and j, if friend j follows friend i (order[j] == order[i] + 1),
# then the arrival time A[j] must be no earlier than the departure time from i plus travel time.
# Departure time from friend i is defined as the meeting start (max(A[i], avail_start)) plus the meeting duration.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by order
    
    print("Optimal meeting schedule:")
    
    # Function to convert minutes to HH:MM format.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting starts at the later of arrival time and the friend's availability start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")