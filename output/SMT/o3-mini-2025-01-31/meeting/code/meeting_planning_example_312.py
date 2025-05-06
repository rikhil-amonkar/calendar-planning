from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between San Francisco locations.
travel = {
    # From Richmond District
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    
    # From Sunset District
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    # From Mission District
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    
    # From Golden Gate Park
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17
}

# Define the friends with their meeting details.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration) in minutes after midnight.
friends = [
    # Sarah: at Sunset District from 10:45AM (645) to 7:00PM (1140); meeting >= 30 minutes.
    ("Sunset District", 645, 1140, 30),
    # Richard: at Haight-Ashbury from 11:45AM (705) to 3:45PM (945); meeting >= 90 minutes.
    ("Haight-Ashbury", 705, 945, 90),
    # Elizabeth: at Mission District from 11:00AM (660) to 5:15PM (1035); meeting >= 120 minutes.
    ("Mission District", 660, 1035, 120),
    # Michelle: at Golden Gate Park from 6:15PM (1095) to 8:45PM (1305); meeting >= 90 minutes.
    ("Golden Gate Park", 1095, 1305, 90)
]

friend_names = ["Sarah", "Richard", "Elizabeth", "Michelle"]
num_friends = len(friends)

# Starting location: You arrive at Richmond District at 9:00AM = 540 minutes after midnight.
start_loc = "Richmond District"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
# x[i]: Bool, whether meeting friend i is scheduled.
# A[i]: Int, the arrival time at the friend's location.
# order[i]: Int, the order index if the meeting is scheduled (0...num_friends-1, or -1 if not scheduled).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, then order[i] must be between 0 and num_friends-1, otherwise it is forced to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that if two meetings are scheduled they have distinct order indices.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Add meeting availability constraints:
# If meeting i is scheduled, it starts at the later of arrival A[i] or the friend's availability start.
# The meeting must finish (starting time plus meeting duration) by the friend's available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints for the first scheduled meeting:
# If friend i is the first meeting (order == 0), the arrival time must be at least start_time plus travel time.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# If friend j follows friend i (i.e., order[j] == order[i] + 1), then arrival time A[j] must be at
# least the departure time from friend i plus the travel time from friend i's location to friend j's location.
# The departure time from friend i is defined as the meeting's start time (max(A[i], avail_start)) plus the meeting duration.
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

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather the scheduled meetings along with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Helper function to convert minutes after midnight into HH:MM format.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting actual start time is the later of the arrival and the friend's available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")