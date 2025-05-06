from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between neighborhoods.
# Locations: Bayview, Nob Hill, Union Square, Chinatown, The Castro, Presidio, Pacific Heights, Russian Hill.
travel = {
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "The Castro"): 20,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Russian Hill"): 13,
    
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Presidio"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Russian Hill"): 14,
    
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Pacific Heights"): 7,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# All times are in minutes after midnight.
# You start at Bayview at 9:00AM (540 minutes).
#
# Friend details:
# Paul:    at Nob Hill      from 4:15PM to 9:15PM    => [16:15 (975), 21:15 (1275)]; min = 60.
# Carol:   at Union Square  from 6:00PM to 8:15PM    => [18:00 (1080), 20:15 (1215)]; min = 120.
# Patricia:at Chinatown     from 8:00PM to 9:30PM    => [20:00 (1200), 21:30 (1290)]; min = 75.
# Karen:   at The Castro    from 5:00PM to 7:00PM    => [17:00 (1020), 19:00 (1140)]; min = 45.
# Nancy:   at Presidio      from 11:45AM to 10:00PM  => [11:45 (705), 22:00 (1320)]; min = 30.
# Jeffrey: at Pacific Heights from 8:00PM to 8:45PM  => [20:00 (1200), 20:45 (1245)]; min = 45.
# Matthew: at Russian Hill  from 3:45PM to 9:45PM    => [15:45 (945), 21:45 (1305)]; min = 75.
friends = [
    ("Nob Hill",      975, 1275, 60),   # Paul
    ("Union Square", 1080, 1215, 120),  # Carol
    ("Chinatown",    1200, 1290, 75),   # Patricia
    ("The Castro",   1020, 1140, 45),   # Karen
    ("Presidio",      705, 1320, 30),   # Nancy
    ("Pacific Heights",1200, 1245, 45),  # Jeffrey
    ("Russian Hill",   945, 1305, 75),   # Matthew
]
friend_names = ["Paul", "Carol", "Patricia", "Karen", "Nancy", "Jeffrey", "Matthew"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting location and time.
start_loc = "Bayview"
start_time = 540  # 9:00 AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
#   x[i]: Bool, True if you decide to meet friend i.
#   A[i]: Int, arrival time (in minutes) at friend i's location.
#   order[i]: Int, the visitation order if friend i is met (if scheduled order in [0, num_friends-1], else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, assign a visitation order if scheduled, otherwise fix order to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Each meeting must finish within the available time window.
# The meeting actually starts at the later of your arrival or the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# Ensure travel time from the starting location to the first meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, ensure that if friend j is scheduled immediately after friend i then the arrival time accounts for meeting duration and travel time.
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

# ----------------------------------------------------------------------------
# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings sorted by their order.
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()
    
    # Convert minutes to HH:MM format.
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in scheduled:
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