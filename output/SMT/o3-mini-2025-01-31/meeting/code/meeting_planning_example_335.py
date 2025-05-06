from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between neighborhoods.
travel = {
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Mission District"): 10,
    
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Alamo Square"): 11,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Helen:  North Beach;     available 9:00AM (540) to 5:00PM (1020), min_duration = 15.
# Betty:  Financial District; available 7:00PM (1140) to 9:45PM (1185), min_duration = 90.
# Amanda: Alamo Square;    available 7:45PM (1185) to 9:00PM (1260), min_duration = 60.
# Kevin:  Mission District; available 10:45AM (645) to 2:45PM (885), min_duration = 45.
friends = [
    ("North Beach",       540, 1020, 15),   # Helen
    ("Financial District",1140, 1185, 90),   # Betty
    ("Alamo Square",      1185, 1260, 60),   # Amanda
    ("Mission District",  645, 885, 45),     # Kevin
]
friend_names = ["Helen", "Betty", "Amanda", "Kevin"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Pacific Heights"
start_time = 540  # 9:00 AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For friend i:
#   x[i] : Boolean, True if meeting is scheduled.
#   A[i] : Integer arrival time (minutes after midnight) at the friend's location.
#   order[i] : Integer order if scheduled (0 to num_friends-1); otherwise -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting is scheduled then order must be in [0, num_friends-1], otherwise order equals -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure scheduled meetings have distinct order numbers.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, meeting starts at the later of arrival time A[i] and avail_start.
# Then meeting finishes after the friend’s min_duration; it must finish no later than avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0) ensure enough travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    ttime = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + ttime))

# For consecutive scheduled meetings, if friend j immediately follows friend i then:
#   your arrival at j must be at least the departure time from i (meeting start + duration) plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings and sort them by visitation order.
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
    for ord_val, i in scheduled:
        loc, avail_start, avail_end, dur = friends[i]
        arr_time = model.evaluate(A[i]).as_long()
        meeting_start = arr_time if arr_time >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arr_time)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
        
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")