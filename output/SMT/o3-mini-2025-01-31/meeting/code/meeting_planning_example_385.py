from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Locations: Nob Hill, Presidio, North Beach, Fisherman's Wharf, Pacific Heights.
travel = {
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
}

# ----------------------------------------------------------------------------
# Define friends data.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
#
# Jeffrey: at Presidio from 8:00AM to 10:00AM => [480, 600], duration = 105 minutes.
# Steven: at North Beach from 1:30PM to 10:00PM => [810, 1320], duration = 45 minutes.
# Barbara: at Fisherman's Wharf from 6:00PM to 9:30PM => [1080, 1290], duration = 30 minutes.
# John: at Pacific Heights from 9:00AM to 1:30PM   => [540, 810], duration = 15 minutes.
friends = [
    ("Presidio",         480, 600, 105),  # Jeffrey
    ("North Beach",      810, 1320, 45),  # Steven
    ("Fisherman's Wharf",1080, 1290, 30),  # Barbara
    ("Pacific Heights",  540, 810, 15),    # John
]
friend_names = ["Jeffrey", "Steven", "Barbara", "John"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Nob Hill"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
#   x[i]: Bool variable indicating whether friend i is scheduled.
#   A[i]: Int variable indicating arrival time (in minutes) at friend i's location.
#   order[i]: Int variable for visit order if friend i is scheduled.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order must be in [0, num_friends-1], else order = -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings have different order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend scheduled, ensure the meeting fits in the friend's available window.
# The meeting starts at the later of (arrival time) or (friend's available start).
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), impose travel from start.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, if friend j follows friend i then ensure:
# arrival_j >= (meeting start of i + duration of i) + travel time from location i to location j.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings, sort them by their order.
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
    for order_val, i in scheduled:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {order_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")