from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Keys are (From, To)
travel = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
#
# Sarah:   North Beach:   available 4:00PM (960)  to 6:15PM (1095), meeting >= 60 minutes.
# Jeffrey: Union Square:  available 3:00PM (900)  to 10:00PM (1320), meeting >= 75 minutes.
# Brian:   Alamo Square:  available 4:00PM (960)  to 5:30PM (1050), meeting >= 75 minutes.
friends = [
    ("North Beach",   960, 1095, 60),  # Sarah
    ("Union Square",  900, 1320, 75),  # Jeffrey
    ("Alamo Square",  960, 1050, 75)   # Brian
]
friend_names = ["Sarah", "Jeffrey", "Brian"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Sunset District"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]    : Bool; True if meeting with friend i is scheduled.
#   A[i]    : Int; arrival time (in minutes after midnight) at friend i's location.
#   order[i]: Int; ordering number in the itinerary if scheduled; if not, fixed to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled, assign order in [0, num_friends-1]. If not, order[i] is fixed to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i, if scheduled, enforce meeting time window.
# Meeting start = max( A[i], avail_start )
# And meeting finish = meeting start + min_duration must be <= avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), enforce travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # Travel time from start (Sunset District) to friend i's location.
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if friend j follows friend i, then ensure that you have
# enough travel time from friend i's location to j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        # Meeting i starts at max(A[i], avail_start_i) and ends after the meeting duration.
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        t_time = travel[(loc_i, loc_j)]
        # If friend j immediately follows friend i then A[j] must be at least departure_i + travel time.
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + t_time))

# --------------------------------------------------------------------
# Objective: Maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # order by scheduled order

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
        print(f"    Arrival: {to_time(arrival)}")
        print(f"    Meeting: {to_time(start_meet)} to {to_time(end_meet)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")