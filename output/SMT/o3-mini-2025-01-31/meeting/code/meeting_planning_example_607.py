from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between neighborhoods.
# The neighborhoods: Sunset District, Russian Hill, The Castro, Richmond District,
# Marina District, North Beach, Union Square, Golden Gate Park.
travel = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Union Square"): 22,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# All times are in minutes after midnight.
# Karen:     at Russian Hill,  available 8:45PM (1245) to 9:45PM (1305), min_duration = 60.
# Jessica:   at The Castro,    available 3:45PM (945) to 7:30PM (1170), min_duration = 60.
# Matthew:   at Richmond District, available 7:30AM (450) to 3:15PM (915), min_duration = 15.
# Michelle:  at Marina District, available 10:30AM (630) to 6:45PM (1125), min_duration = 75.
# Carol:     at North Beach,     available 12:00PM (720) to 5:00PM (1020), min_duration = 90.
# Stephanie: at Union Square,    available 10:45AM (645) to 2:15PM (855), min_duration = 30.
# Linda:     at Golden Gate Park, available 10:45AM (645) to 10:00PM (1320), min_duration = 90.
friends = [
    ("Russian Hill",    1245, 1305, 60),   # Karen
    ("The Castro",      945, 1170, 60),    # Jessica
    ("Richmond District",450, 915, 15),     # Matthew
    ("Marina District", 630, 1125, 75),     # Michelle
    ("North Beach",     720, 1020, 90),     # Carol
    ("Union Square",    645, 855, 30),      # Stephanie
    ("Golden Gate Park",645, 1320, 90),     # Linda
]
friend_names = ["Karen", "Jessica", "Matthew", "Michelle", "Carol", "Stephanie", "Linda"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Sunset District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
#   x[i]     : Boolean, indicating if meeting i is scheduled.
#   A[i]     : Integer, representing arrival time at friend i's location (in minutes).
#   order[i] : Integer, representing the order if meeting is scheduled (0 to num_friends-1), else -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting scheduled then order in [0, num_friends-1]; if not, order equals -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure all scheduled meetings have distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, the meeting start time is the later of your arrival A[i] and the friend's avail_start.
# The meeting will finish after the min_duration, and must end no later than avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure you allow for travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For two consecutive meetings: if friend j is visited immediately after friend i,
# then your arrival at j must be at least the departure time from i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i   # meeting i ends after its duration
        travel_time_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings and sort them according to their assigned order.
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
        arr = model.evaluate(A[i]).as_long()
        meeting_start = arr if arr >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arr)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")