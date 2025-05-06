from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define the travel times (in minutes, directional) between neighborhoods.
travel = {
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,

    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Mission District"): 20,

    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,

    ("Union Square", "Marina District"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,

    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,

    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,

    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,

    ("Financial District", "Marina District"): 15,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,

    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Mission District"): 11,

    ("Mission District", "Marina District"): 19,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12
}

# Define friend meeting information.
# Each friend is a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Joshua: Embarcadero, 9:45AM to 6:00PM, min 105 minutes.
    ("Embarcadero", 585, 1080, 105),
    # Jeffrey: Bayview, 9:45AM to 8:15PM, min 75 minutes.
    ("Bayview",    585, 1215, 75),
    # Charles: Union Square, 10:45AM to 8:15PM, min 120 minutes.
    ("Union Square",645, 1215, 120),
    # Joseph: Chinatown, 7:00AM to 3:30PM, min 60 minutes.
    ("Chinatown",  420, 930, 60),
    # Elizabeth: Sunset District, 9:00AM to 9:45AM, min 45 minutes.
    ("Sunset District",540, 585, 45),
    # Matthew: Golden Gate Park, 11:00AM to 7:30PM, min 45 minutes.
    ("Golden Gate Park",660, 1170, 45),
    # Carol: Financial District, 10:45AM to 11:15AM, min 15 minutes.
    ("Financial District",645, 675, 15),
    # Paul: Haight-Ashbury, 7:15PM to 8:30PM, min 15 minutes.
    ("Haight-Ashbury",1155, 1230, 15),
    # Rebecca: Mission District, 5:00PM to 9:45PM, min 45 minutes.
    ("Mission District",1020, 1305, 45)
]
num_friends = len(friends)

# Starting conditions:
# You arrive at Marina District at 9:00AM, i.e. 540 minutes after midnight.
start_loc = "Marina District"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, define decision variables:
#   x[i]: Bool indicating if meeting friend i is scheduled.
#   A[i]: Integer representing arrival time at friend i's location.
#   order[i]: Integer indicating the order of friend i in the schedule (0..num_friends-1), or -1 if not scheduled.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

for i in range(num_friends):
    # When friend is scheduled, order must be between 0 and num_friends-1.
    # When not scheduled, order is -1.
    opt.add(If(x[i], And(order[i] >= 0, order[i] < num_friends), order[i] == -1))
    # Arrival times must be nonnegative.
    opt.add(A[i] >= 0)

# Each scheduled meeting must have a unique order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, enforce meeting availability:
# Let meeting start = max(arrival time, friend’s avail_start); then meeting must end (meeting_start+min_duration) by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints from the start:
# For the first scheduled meeting (order==0), ensure arrival time is at least (start_time + travel time from start location).
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # Travel from Marina District (start_loc) to friend i's location.
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if friend j immediately follows friend i, then
# arrival time at j must be at least departure time from i plus travel time.
# Departure from i is defined as: max(A[i], avail_start_i) + min_dur_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_i, _, dur_i = friends[i]
        loc_j, avail_j, _, _ = friends[j]
        depart_i = If(A[i] < avail_i, avail_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= depart_i + t_time))

# Objective is to maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and output the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings with their order index.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    print("Optimal meeting schedule:")
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Joshua", "Jeffrey", "Charles", "Joseph", "Elizabeth", 
                    "Matthew", "Carol", "Paul", "Rebecca"]
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, min_dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts when both you have arrived and the friend is available.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + min_dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")