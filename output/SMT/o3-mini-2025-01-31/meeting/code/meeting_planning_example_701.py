from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Keys are tuples: (From, To)
travel = {
    # From Mission District
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    
    # From The Castro
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,
    
    # From Nob Hill
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,
    
    # From Presidio
    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    
    # From Marina District
    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    
    # From Pacific Heights
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    
    # From Golden Gate Park
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    
    # From Chinatown
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    
    # From Richmond District
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# --------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Times are in minutes after midnight.
# Lisa:      at The Castro        from 7:15PM to 9:15PM,  min meeting = 120 minutes.
# Daniel:    at Nob Hill          from 8:15AM to 11:00AM, min meeting = 15 minutes.
# Elizabeth: at Presidio          from 9:15PM to 10:15PM, min meeting = 45 minutes.
# Steven:    at Marina District   from 4:30PM to 8:45PM,  min meeting = 90 minutes.
# Timothy:   at Pacific Heights   from 12:00PM to 6:00PM,  min meeting = 90 minutes.
# Ashley:    at Golden Gate Park   from 8:45PM to 9:45PM,  min meeting = 60 minutes.
# Kevin:     at Chinatown         from 12:00PM to 7:00PM,  min meeting = 30 minutes.
# Betty:     at Richmond District from 1:15PM to 3:45PM,   min meeting = 30 minutes.
friends = [
    ("The Castro",       1155, 1275, 120),  # Lisa
    ("Nob Hill",           495,  660, 15),   # Daniel
    ("Presidio",         1275, 1335, 45),    # Elizabeth
    ("Marina District",   990, 1245, 90),    # Steven
    ("Pacific Heights",   720, 1080, 90),    # Timothy
    ("Golden Gate Park", 1245, 1305, 60),    # Ashley
    ("Chinatown",         720, 1140, 30),    # Kevin
    ("Richmond District", 795, 945, 30),     # Betty
]
friend_names = ["Lisa", "Daniel", "Elizabeth", "Steven", "Timothy", "Ashley", "Kevin", "Betty"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Mission District"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables for each friend i:
#   x[i]    : Bool, True if meeting with friend i is scheduled.
#   A[i]    : Int, arrival time (in minutes after midnight) at friend i's location.
#   order[i]: Int, index in the itinerary if scheduled; if not scheduled, fixed to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled, assign an order in [0, num_friends-1]; if not, order = -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend i that is scheduled, ensure the meeting fits within the available window.
# Meeting start time is the later of your arrival A[i] and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), enforce travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if friend j immediately follows friend i (order[j] = order[i] + 1),
# then the arrival time at j must be at least the departure time from meeting i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        t_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + t_time))

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
    schedule.sort()  # sort by order index

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
        print(f"    Meeting Time: {to_time(start_meet)} to {to_time(end_meet)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")