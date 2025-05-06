from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "The Castro"): 22,
    
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is a tuple (location, avail_start, avail_end, min_duration)
# All times are in minutes after midnight.
# You start at Union Square at 9:00AM (540 minutes).
friends = [
    # 0: Andrew at Golden Gate Park: 11:45AM to 2:30PM (705 to 870), min 75 minutes.
    ("Golden Gate Park", 705, 870, 75),
    # 1: Sarah at Pacific Heights: 4:15PM to 6:45PM (975 to 1125), min 15 minutes.
    ("Pacific Heights", 975, 1125, 15),
    # 2: Nancy at Presidio: 5:30PM to 7:15PM (1050 to 1155), min 60 minutes.
    ("Presidio", 1050, 1155, 60),
    # 3: Rebecca at Chinatown: 9:45AM to 9:30PM (585 to 1290), min 90 minutes.
    ("Chinatown", 585, 1290, 90),
    # 4: Robert at The Castro: 8:30AM to 2:15PM (510 to 855), min 30 minutes.
    ("The Castro", 510, 855, 30),
]
friend_names = ["Andrew", "Sarah", "Nancy", "Rebecca", "Robert"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Union Square"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] : Boolean variable, True if meeting friend i is scheduled.
# A[i] : Arrival time at friend i's location.
# order[i] : Order in which friend i is visited; if not meeting then set to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a friend meeting is scheduled then order[i] should be in [0, num_friends-1],
# otherwise, order[i] is set to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For each scheduled meeting, the meeting starts at the later of your arrival A[i]
# and the friend’s available start time. Then meeting must last at least the required duration.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location for the first scheduled meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel.get((start_loc, loc), 0)
    # If friend i is scheduled first, then arrival time must be at least start_time + travel time.
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If friend j is visited immediately after friend i then
# your arrival time at friend j must be at least the departure time from i
# (meeting start for i + meeting duration_i) plus the travel time from i to j.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: Maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings in order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        start_meeting = arrival if arrival >= avail_start else avail_start
        meeting_end = start_meeting + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(start_meeting)} - {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")