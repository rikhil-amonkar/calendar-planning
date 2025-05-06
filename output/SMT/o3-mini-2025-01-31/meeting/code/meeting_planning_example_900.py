from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Locations:
# Richmond District, The Castro, Nob Hill, Marina District, Pacific Heights,
# Haight-Ashbury, Mission District, Chinatown, Russian Hill, Alamo Square, Bayview.
travel = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,

    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,

    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,

    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,

    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,

    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,

    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,

    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,

    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,

    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,

    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Starting time is 9:00AM = 540 minutes.
#
# Friend details:
# Matthew: at The Castro from 4:30PM to 8:00PM.       16:30 = 990, 20:00 = 1200, min = 45.
# Rebecca: at Nob Hill from 3:15PM to 7:15PM.            15:15 = 915, 19:15 = 1155, min = 105.
# Brian: at Marina District from 2:15PM to 10:00PM.       14:15 = 855, 22:00 = 1320, min = 30.
# Emily: at Pacific Heights from 11:15AM to 7:45PM.       11:15 = 675, 19:45 = 1185, min = 15.
# Karen: at Haight-Ashbury from 11:45AM to 5:30PM.         11:45 = 705, 17:30 = 1050, min = 30.
# Stephanie: at Mission District from 1:00PM to 3:45PM.    13:00 = 780, 15:45 = 945, min = 75.
# James: at Chinatown from 2:30PM to 7:00PM.              14:30 = 870, 19:00 = 1140, min = 120.
# Steven: at Russian Hill from 2:00PM to 8:00PM.           14:00 = 840, 20:00 = 1200, min = 30.
# Elizabeth: at Alamo Square from 1:00PM to 5:15PM.       13:00 = 780, 17:15 = 1035, min = 120.
# William: at Bayview from 6:15PM to 8:15PM.              18:15 = 1095, 20:15 = 1215, min = 90.
friends = [
    ("The Castro",     990, 1200, 45),    # Matthew
    ("Nob Hill",       915, 1155, 105),   # Rebecca
    ("Marina District",855, 1320, 30),    # Brian
    ("Pacific Heights",675, 1185, 15),    # Emily
    ("Haight-Ashbury", 705, 1050, 30),    # Karen
    ("Mission District",780, 945, 75),     # Stephanie
    ("Chinatown",      870, 1140, 120),   # James
    ("Russian Hill",   840, 1200, 30),    # Steven
    ("Alamo Square",   780, 1035, 120),   # Elizabeth
    ("Bayview",       1095, 1215, 90),    # William
]
friend_names = ["Matthew", "Rebecca", "Brian", "Emily", "Karen", "Stephanie", "James", "Steven", "Elizabeth", "William"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Richmond District"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] : Bool, True if meeting with friend i is scheduled.
# A[i] : Int, arrival time (in minutes) at friend i's location.
# order[i]: Int, the visitation order if scheduled (in [0, num_friends-1]); otherwise fixed to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Each friend, if scheduled, must be assigned an order between 0 and num_friends-1;
# otherwise the order is fixed to -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Scheduled meetings must have distinct orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, ensure it fits within the friend’s time window.
# The meeting starts at the later of your arrival time and the friend's available start.
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
# If friend j is visited immediately after friend i, ensure that travel time is considered.
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
# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal schedule.
result = opt.check()
if result == sat:
    model = opt.model()
    # Gather scheduled meetings, sorted by the order index.
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