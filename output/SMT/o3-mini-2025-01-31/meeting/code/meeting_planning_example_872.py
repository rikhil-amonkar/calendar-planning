from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between San Francisco neighborhoods.
# Locations: Presidio, Haight-Ashbury, Nob Hill, Russian Hill, North Beach,
# Chinatown, Union Square, Embarcadero, Financial District, Marina District.
travel = {
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,

    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Haight-Ashbury"): 0,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Marina District"): 17,

    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Marina District"): 11,

    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,

    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,

    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Marina District"): 12,

    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,

    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,

    ("Financial District", "Presidio"): 22,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,

    ("Marina District", "Presidio"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Starting at Presidio at 9:00AM = 540 minutes.
# Friend details:
# Karen: at Haight-Ashbury from 9:00PM to 9:45PM    => 9:00PM = 1260, 9:45PM = 1305; min = 45.
# Jessica: at Nob Hill from 1:45PM to 9:00PM         => 1:45PM = 825, 9:00PM = 1260; min = 90.
# Brian: at Russian Hill from 3:30PM to 9:45PM         => 3:30PM = 930, 9:45PM = 1305; min = 60.
# Kenneth: at North Beach from 9:45AM to 9:00PM        => 9:45AM = 585, 9:00PM = 1260; min = 30.
# Jason: at Chinatown from 8:15AM to 11:45AM           => 8:15AM = 495, 11:45AM = 705; min = 75.
# Stephanie: at Union Square from 2:45PM to 6:45PM      => 2:45PM = 885, 6:45PM = 1125; min = 105.
# Kimberly: at Embarcadero from 9:45AM to 7:30PM        => 9:45AM = 585, 7:30PM = 1170; min = 75.
# Steven: at Financial District from 7:15AM to 9:15PM    => 7:15AM = 435, 9:15PM = 1275; min = 60.
# Mark: at Marina District from 10:15AM to 1:00PM       => 10:15AM = 615, 1:00PM = 780; min = 75.
friends = [
    ("Haight-Ashbury", 1260, 1305, 45),   # Karen
    ("Nob Hill",       825, 1260, 90),      # Jessica
    ("Russian Hill",   930, 1305, 60),      # Brian
    ("North Beach",    585, 1260, 30),      # Kenneth
    ("Chinatown",      495, 705, 75),       # Jason
    ("Union Square",   885, 1125, 105),     # Stephanie
    ("Embarcadero",    585, 1170, 75),      # Kimberly
    ("Financial District", 435, 1275, 60),  # Steven
    ("Marina District",    615, 780, 75),    # Mark
]
friend_names = ["Karen", "Jessica", "Brian", "Kenneth", "Jason", "Stephanie", "Kimberly", "Steven", "Mark"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting location and time.
start_loc = "Presidio"
start_time = 540  # 9:00 AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
#  x[i] : Bool, True if meeting with friend i is scheduled.
#  A[i] : Int, arrival time (in minutes after midnight) at friend i's location.
#  order[i] : Int, visitation order for friend i if scheduled (from 0 to num_friends-1); otherwise -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then assign order in [0, num_friends-1], else order = -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, ensure the meeting fits inside the friend's available window.
# The meeting starts at the later of (arrival time A[i]) and available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), enforce travel from start.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings:
# If friend j follows friend i (i.e. order[j] = order[i] + 1) then travel time must be observed.
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
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    # Create a list of scheduled meetings sorted by order.
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