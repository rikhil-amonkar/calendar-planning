from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Sunset District"): 26,
    
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Sunset District"): 24,
    
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Sunset District"): 23,
    
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Bayview"): 22
}

# Define friend meeting details as tuples:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Rebecca: at Mission District from 11:30AM (690) to 8:15PM (1215); meeting >= 120 minutes.
    ("Mission District", 690, 1215, 120),
    # Karen: at Bayview from 12:45PM (765) to 3:00PM (900); meeting >= 120 minutes.
    ("Bayview", 765, 900, 120),
    # Carol: at Sunset District from 10:15AM (615) to 11:45AM (705); meeting >= 30 minutes.
    ("Sunset District", 615, 705, 30)
]
friend_names = ["Rebecca", "Karen", "Carol"]
num_friends = len(friends)

# Starting conditions:
# You arrive at Union Square at 9:00AM, which is 540 minutes after midnight.
start_loc = "Union Square"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For each friend i,
#   x[i]    : Bool indicating if the meeting is scheduled.
#   A[i]    : Int representing your arrival time at friend i's location.
#   order[i]: Int representing the meeting order, if scheduled; otherwise -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constrain order variables:
# If meeting i is scheduled then order[i] is in [0, num_friends-1];
# otherwise it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Each meeting must occur within the friend’s available time window.
# The effective meeting start time is the later of your arrival time and the friend’s avail_start.
# The meeting must finish (meeting start + min_duration) by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any friend i scheduled as the first meeting (order[i]==0),
# your arrival time A[i] must be at least the start time plus the travel time from start_loc.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Travel constraints between consecutive meetings:
# If meeting j immediately follows meeting i (i.e., order[j] == order[i] + 1),
# then your arrival time at meeting j must be at least the departure time from meeting i
# (which is the meeting start time for i plus its duration) plus
# the travel time from location i to location j.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization problem and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Format minutes after midnight to HH:MM.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")