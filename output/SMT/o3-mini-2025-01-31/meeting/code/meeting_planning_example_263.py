from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10
}

# Define friend meeting details.
# Each friend is represented as:
# (location, avail_start, avail_end, min_duration) 
# Times are in minutes after midnight.
friends = [
    # Betty: Embarcadero from 7:45PM to 9:45PM; meeting >= 15 minutes.
    ("Embarcadero", 1185, 1305, 15),
    # Karen: Fisherman's Wharf from 8:45AM to 3:00PM; meeting >= 30 minutes.
    ("Fisherman's Wharf", 525, 900, 30),
    # Anthony: Financial District from 9:15AM to 9:30PM; meeting >= 105 minutes.
    ("Financial District", 555, 1290, 105)
]
friend_names = ["Betty", "Karen", "Anthony"]
num_friends = len(friends)

# Starting point: You arrive at Bayview at 9:00AM = 540 minutes after midnight.
start_loc = "Bayview"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
# x[i]: a Boolean to decide if meeting friend i is scheduled.
# A[i]: an integer representing the arrival time at friend i's location.
# order[i]: an integer representing the order in which friend i is visited.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constraint: If x[i] is true (meeting scheduled) then order[i] is in [0, num_friends-1],
# otherwise we force order[i] to -1. And arrival times must be non-negative.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Distinct order numbers for scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if the meeting is scheduled, then meeting starts at the later of the arrival time
# or the friend’s availability start, and it finishes within their availability window.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints:
# For the first scheduled meeting (order == 0), you must travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if friend j immediately follows friend i then you must allow for travel.
# Departure time from friend i is defined as meeting's start time plus its duration.
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

# Objective: maximize the total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings and sort them by their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Helper function to convert minutes after midnight into HH:MM format.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts at the maximum of the arrival time or friend availability.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")