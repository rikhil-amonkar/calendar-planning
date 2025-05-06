from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Location names for clarity.
# Locations:
# "Financial District", "Chinatown", "Golden Gate Park"
locations = ["Financial District", "Chinatown", "Golden Gate Park"]

# Travel times (in minutes, directional):
travel = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23
}

# Friend meeting information:
# Each entry is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes from midnight.
# Kenneth: at Chinatown from 12:00PM (720) to 3:00PM (900), minimum meeting 90 minutes.
# Barbara: at Golden Gate Park from 8:15AM (495) to 7:00PM (1140), minimum meeting 45 minutes.
friends = [
    ("Chinatown", 720, 900, 90),    # Kenneth
    ("Golden Gate Park", 495, 1140, 45)  # Barbara
]
num_friends = len(friends)

# Starting conditions: You arrive at Financial District at 9:00AM = 540 minutes.
start_loc = "Financial District"
start_time = 540

# Create the Z3 optimizer instance.
opt = Optimize()

# Decision variables for each friend i:
#   x[i] indicates if the meeting is scheduled.
#   A[i] is the arrival time (in minutes) at the friend's location.
#   order[i] is the position in the meeting order if scheduled (0..num_friends-1) or -1 if not.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # If meeting is scheduled, then order is between 0 and num_friends-1, else order == -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    opt.add(A[i] >= 0)

# Enforce distinct meeting orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# For each meeting, the effective start is the later of your arrival time and the friend's avail_start.
# Then, meeting must last at least the specified duration and end by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    effective_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), effective_start + dur <= avail_end))

# Travel constraints:
# For the first meeting in the order (order == 0), you must travel from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))
    
# For consecutive meetings: if friend j is immediately after friend i then your arrival time for j must be
# at least the departure time from i plus travel time.
# Define departure time from friend i as max(A[i], avail_start_i) + meeting duration.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        travel_time = travel[(loc_i, loc_j)]
        # If friend j's order is exactly one more than friend i's order, enforce travel time.
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time))

# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append( (model.evaluate(order[i]).as_long(), i) )
    schedule.sort()
    
    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Kenneth", "Barbara"]
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting starts at the later of arrival and availability start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")