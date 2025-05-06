from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From Golden Gate Park
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    
    # From The Castro
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Russian Hill"): 18,
    
    # From Chinatown
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,
    
    # From Alamo Square
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    
    # From North Beach
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Russian Hill"): 4,
    
    # From Russian Hill
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5
}

# Define friend meeting details.
# Each friend is represented as a tuple:
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Carol: at Haight-Ashbury from 9:30PM (1290) to 10:30PM (1350); meeting >= 60 minutes.
    ("Haight-Ashbury", 1290, 1350, 60),
    # Laura: at Fisherman's Wharf from 11:45AM (705) to 9:30PM (1290); meeting >= 60 minutes.
    ("Fisherman's Wharf", 705, 1290, 60),
    # Karen: at The Castro from 7:15AM (435) to 2:00PM (840); meeting >= 75 minutes.
    ("The Castro", 435, 840, 75),
    # Elizabeth: at Chinatown from 12:15PM (735) to 9:30PM (1290); meeting >= 75 minutes.
    ("Chinatown", 735, 1290, 75),
    # Deborah: at Alamo Square from 12:00PM (720) to 3:00PM (900); meeting >= 105 minutes.
    ("Alamo Square", 720, 900, 105),
    # Jason: at North Beach from 2:45PM (885) to 7:00PM (1140); meeting >= 90 minutes.
    ("North Beach", 885, 1140, 90),
    # Steven: at Russian Hill from 2:45PM (885) to 6:30PM (1110); meeting >= 120 minutes.
    ("Russian Hill", 885, 1110, 120)
]
friend_names = ["Carol", "Laura", "Karen", "Elizabeth", "Deborah", "Jason", "Steven"]
num_friends = len(friends)

# Starting conditions:
# You arrive at Golden Gate Park at 9:00AM = 540 minutes after midnight.
start_loc = "Golden Gate Park"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend i, create decision variables:
# x[i] : Bool indicating whether the meeting is scheduled.
# A[i] : Int representing the arrival time at friend i's location.
# order[i] : Int representing the order of the meeting (if scheduled then in [0, num_friends-1], else forced to -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting is scheduled then order must be in [0, num_friends-1], otherwise order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that any two scheduled meetings get distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# If meeting i is scheduled, then it starts at the later of your arrival time A[i] or the friend's available start.
# The meeting (start time + min_duration) must finish by the available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# If meeting i is the first scheduled (order[i] == 0), then your arrival time A[i]
# must be no earlier than the start time plus travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# For any two scheduled meetings i and j, if meeting j immediately follows meeting i
# (order[j] == order[i] + 1), then the arrival time for meeting j must be at least the
# departure time from meeting i plus the travel time from i's location to j's location.
# We define the departure time from meeting i as the meeting start (max(A[i], avail_start))
# plus the meeting's minimum duration.
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

# Solve the optimization problem and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with their order values.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by scheduled order
        
    print("Optimal meeting schedule:")
    
    # Helper: convert minutes after midnight to HH:MM format.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting starts at the later of your arrival and the friend's available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")