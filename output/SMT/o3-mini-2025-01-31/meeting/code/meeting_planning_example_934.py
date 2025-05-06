from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From Nob Hill
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    
    # From Embarcadero
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    
    # From The Castro
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    # From Union Square
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    
    # From North Beach
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    
    # From Pacific Heights
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    
    # From Chinatown
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    
    # From Golden Gate Park
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    # From Marina District
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    
    # From Russian Hill
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7
}

# Define friend meeting details.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Mary: at Embarcadero from 20:00 (1200) to 21:15 (1275); meeting >= 75 minutes.
    ("Embarcadero", 1200, 1275, 75),
    # Kenneth: at The Castro from 11:15 (675) to 19:15 (1155); meeting >= 30 minutes.
    ("The Castro", 675, 1155, 30),
    # Joseph: at Haight-Ashbury from 20:00 (1200) to 22:00 (1320); meeting >= 120 minutes.
    ("Haight-Ashbury", 1200, 1320, 120),
    # Sarah: at Union Square from 11:45 (705) to 14:30 (870); meeting >= 90 minutes.
    ("Union Square", 705, 870, 90),
    # Thomas: at North Beach from 19:15 (1155) to 19:45 (1185); meeting >= 15 minutes.
    ("North Beach", 1155, 1185, 15),
    # Daniel: at Pacific Heights from 13:45 (825) to 20:30 (1230); meeting >= 15 minutes.
    ("Pacific Heights", 825, 1230, 15),
    # Richard: at Chinatown from 8:00 (480) to 18:45 (1125); meeting >= 30 minutes.
    ("Chinatown", 480, 1125, 30),
    # Mark: at Golden Gate Park from 17:30 (1050) to 21:30 (1290); meeting >= 120 minutes.
    ("Golden Gate Park", 1050, 1290, 120),
    # David: at Marina District from 20:00 (1200) to 21:00 (1260); meeting >= 60 minutes.
    ("Marina District", 1200, 1260, 60),
    # Karen: at Russian Hill from 13:15 (795) to 18:30 (1110); meeting >= 120 minutes.
    ("Russian Hill", 795, 1110, 120)
]
friend_names = ["Mary", "Kenneth", "Joseph", "Sarah", "Thomas", "Daniel", "Richard", "Mark", "David", "Karen"]
num_friends = len(friends)

# Starting conditions:
# You arrive at Nob Hill at 9:00AM = 540 minutes after midnight.
start_loc = "Nob Hill"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
# For each friend i:
#   x[i]    : Bool indicating if the meeting is scheduled.
#   A[i]    : Int representing the arrival time at friend i's location.
#   order[i]: Int representing the meeting order (if scheduled, an integer between 0 and num_friends-1; otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constrain each order: if meeting i is scheduled then order[i] is in [0, num_friends-1] else it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings get distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints.
# For each friend, if meeting i is scheduled, then the effective meeting start time is max(A[i], avail_start)
# and the meeting must finish (start time + min_duration) no later than avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any scheduled meeting i with order 0, the arrival time A[i] must be at least start_time + travel time from start_loc.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# For any two scheduled meetings i and j, if meeting j immediately follows meeting i (i.e. order[j] == order[i] + 1),
# then the arrival time at meeting j must be at least the departure time from meeting i plus the travel time.
# The departure time from meeting i is defined as max(A[i], avail_start) + min_duration.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization and print the schedule.
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    print("Optimal meeting schedule:")
    
    # Helper to convert minutes after midnight to HH:MM.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")