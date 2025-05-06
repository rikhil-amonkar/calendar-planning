from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From Pacific Heights
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    
    # From Nob Hill
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 25,
    ("Nob Hill", "Haight-Ashbury"): 13,
    
    # From Russian Hill
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Sunset District"): 24,
    ("Russian Hill", "Haight-Ashbury"): 17,
    
    # From The Castro
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    
    # From Sunset District
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Sunset District"): 15
}

# Define friend meeting details.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are given in minutes after midnight.
friends = [
    # Ronald: at Nob Hill from 10:00AM (600) to 5:00PM (1020); meeting >= 105 minutes.
    ("Nob Hill", 600, 1020, 105),
    # Sarah: at Russian Hill from 7:15AM (435) to 9:30AM (570); meeting >= 45 minutes.
    ("Russian Hill", 435, 570, 45),
    # Helen: at The Castro from 1:30PM (810) to 5:00PM (1020); meeting >= 120 minutes.
    ("The Castro", 810, 1020, 120),
    # Joshua: at Sunset District from 2:15PM (855) to 7:30PM (1170); meeting >= 90 minutes.
    ("Sunset District", 855, 1170, 90),
    # Margaret: at Haight-Ashbury from 10:15AM (615) to 10:00PM (1320); meeting >= 60 minutes.
    ("Haight-Ashbury", 615, 1320, 60)
]
friend_names = ["Ronald", "Sarah", "Helen", "Joshua", "Margaret"]
num_friends = len(friends)

# Starting location: You arrive at Pacific Heights at 9:00AM = 540 minutes after midnight.
start_loc = "Pacific Heights"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
# x[i]: Bool indicating whether meeting friend i is scheduled.
# A[i]: Int representing the arrival time at friend i's location.
# order[i]: Int representing the order index (if scheduled, in 0...num_friends-1; if not, forced to -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Enforce that if meeting is scheduled then order[i] is between 0 and num_friends-1, otherwise order[i] = -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct order indices among scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# If the meeting is scheduled, it will start at the later of your arrival time A[i] or the friend’s availability start.
# The meeting then lasts for at least the minimum duration and must finish by the available end time.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints for the first scheduled meeting (order == 0):
# If friend i is the first meeting, then the arrival time must be at least the starting time plus travel time from start_loc.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# For any two scheduled meetings i and j, if friend j immediately follows friend i (order[j] == order[i] + 1),
# then the arrival time at j must account for the departure from i plus the travel time from i's location to j's location.
# The departure from friend i is defined as the meeting start (max(A[i], avail_start)) plus the duration.
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

# Objective: maximize the number of meetings attended.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization and print the meeting schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings and their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    def to_time(t):
        # Converts minutes after midnight to HH:MM format.
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