from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes)
# Provided distances:
#   Sunset District -> Golden Gate Park = 11 minutes.
#   Golden Gate Park -> Sunset District = 10 minutes.
travel = {
    ("Sunset District", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
}

# --------------------------------------------------------------------
# Friend data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Joshua is at Golden Gate Park from 8:45PM (1245) to 9:45PM (1305), 
# and requires a meeting of at least 15 minutes.
friends = [
    ("Golden Gate Park", 1245, 1305, 15),  # Joshua
]
friend_names = ["Joshua"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Sunset District"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]    : Bool, True if meeting with friend i is scheduled.
#   A[i]    : Int, arrival time at friend i's location (in minutes after midnight).
#   order[i]: Int, the meeting order (if scheduled, order in [0, num_friends-1]; otherwise, -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order is in [0, num_friends-1], else it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# For each pair of friends, ensure that if both are scheduled they have distinct orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i that is scheduled, enforce the meeting to take place within the available window.
# The meeting actually starts at: meeting_start = max(A[i], avail_start).
# Then the meeting must finish (meeting_start + min_duration) on or before avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), you must travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# --------------------------------------------------------------------
# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by order

    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        start_meet = arrival if arrival >= avail_start else avail_start
        end_meet = start_meet + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(start_meet)} - {to_time(end_meet)}")
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")