from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between neighborhoods.
# Locations: Chinatown, Mission District, Alamo Square, Pacific Heights,
#            Union Square, Golden Gate Park, Sunset District, Presidio.
travel = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,

    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,

    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,

    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,

    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,

    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,

    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,

    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
#
# David:     at Mission District from 8:00AM to 7:45PM   => [480, 1185], min_duration = 45.
# Kenneth:   at Alamo Square from 2:00PM to 7:45PM       => [840, 1185], min_duration = 120.
# John:      at Pacific Heights from 5:00PM to 8:00PM      => [1020, 1200], min_duration = 15.
# Charles:   at Union Square from 9:45PM to 10:45PM        => [1305, 1365], min_duration = 60.
# Deborah:   at Golden Gate Park from 7:00AM to 6:15PM      => [420, 1095], min_duration = 90.
# Karen:     at Sunset District from 5:45PM to 9:15PM       => [1065, 1275], min_duration = 15.
# Carol:     at Presidio from 8:15AM to 9:15AM             => [495, 555], min_duration = 30.
friends = [
    ("Mission District", 480, 1185, 45),   # David
    ("Alamo Square",     840, 1185, 120),  # Kenneth
    ("Pacific Heights", 1020, 1200, 15),    # John
    ("Union Square",    1305, 1365, 60),     # Charles
    ("Golden Gate Park",420, 1095, 90),      # Deborah
    ("Sunset District", 1065, 1275, 15),     # Karen
    ("Presidio",         495, 555, 30),       # Carol
]
friend_names = ["David", "Kenneth", "John", "Charles", "Deborah", "Karen", "Carol"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Chinatown"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
#   x[i]: Bool, True if meeting with friend i is scheduled.
#   A[i]: Int, arrival time (in minutes) at friend i's location.
#   order[i]: Int, meeting visitation order if scheduled (from 0 to num_friends-1), else -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, its order must be in [0, num_friends-1], otherwise -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend (if scheduled), the meeting starts at the later of your arrival and the friend's avail_start.
# The meeting must finish (start time + min_duration) no later than the friend's avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure sufficient travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings (if friend j immediately follows friend i), ensure that travel time is observed.
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
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings and sort them by their order.
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
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")