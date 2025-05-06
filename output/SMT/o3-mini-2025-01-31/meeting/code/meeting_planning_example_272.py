from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations:
# The locations are: Russian Hill, Nob Hill, Mission District, Embarcadero.
travel = {
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Embarcadero"): 8,

    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Embarcadero"): 9,

    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Embarcadero"): 19,

    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Time is in minutes after midnight.
# Patricia: at Nob Hill from 6:30PM to 9:45PM (1110 to 1305) - meeting duration at least 90 minutes.
# Ashley: at Mission District from 8:30PM to 9:15PM (1230 to 1275) - meeting duration at least 45 minutes.
# Timothy: at Embarcadero from 9:45AM to 5:45PM (585 to 1065) - meeting duration at least 120 minutes.
friends = [
    ("Nob Hill",        1110, 1305, 90),   # Patricia
    ("Mission District",1230, 1275, 45),   # Ashley
    ("Embarcadero",      585, 1065, 120),  # Timothy
]
friend_names = ["Patricia", "Ashley", "Timothy"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Russian Hill"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]: Bool - True if the meeting with friend i is scheduled.
#   A[i]: Int  - Arrival time (in minutes) at friend i's location.
#   order[i]: Int - The order in which friend i is visited (if scheduled, in [0, num_friends-1]; if not, fixed to -1).
x     = [Bool(f"x_{i}") for i in range(num_friends)]
A     = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a friend is scheduled, assign an order in [0, num_friends-1], otherwise fix order to -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure distinct order numbers for scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i that is scheduled, ensure that the meeting fits into the available window.
# The meeting starts at the later of your arrival A[i] and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), enforce travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings:
# If friend j is visited immediately after friend i, the arrival at j must be at least the departure time from i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# --------------------------------------------------------------------
# Objective: Maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by the order of visits

    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
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
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")