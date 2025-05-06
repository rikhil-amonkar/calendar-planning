from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From The Castro
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,
    
    # From Presidio
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,
    
    # From Sunset District
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    # From Mission District
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Russian Hill"): 15,
    
    # From Golden Gate Park
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    # From Russian Hill
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21
}

# Define friend meeting details.
# Each friend is represented by a tuple:
# (location, avail_start, avail_end, min_duration)
# Times (in minutes after midnight):
#   9:00AM is 540, 10:00AM is 600, 1:15PM is 795, etc.
friends = [
    # Rebecca: at Presidio from 6:15PM (1095) to 8:45PM (1245); meeting >= 60 minutes.
    ("Presidio", 1095, 1245, 60),
    # Linda: at Sunset District from 3:30PM (930) to 7:45PM (1185); meeting >= 30 minutes.
    ("Sunset District", 930, 1185, 30),
    # Elizabeth: at Haight-Ashbury from 5:15PM (1035) to 7:30PM (1170); meeting >= 105 minutes.
    ("Haight-Ashbury", 1035, 1170, 105),
    # William: at Mission District from 1:15PM (795) to 7:30PM (1170); meeting >= 30 minutes.
    ("Mission District", 795, 1170, 30),
    # Robert: at Golden Gate Park from 2:15PM (855) to 9:30PM (1290); meeting >= 45 minutes.
    ("Golden Gate Park", 855, 1290, 45),
    # Mark: at Russian Hill from 10:00AM (600) to 9:15PM (1275); meeting >= 75 minutes.
    ("Russian Hill", 600, 1275, 75)
]
friend_names = ["Rebecca", "Linda", "Elizabeth", "William", "Robert", "Mark"]
num_friends = len(friends)

# Starting conditions:
# You arrive at The Castro at 9:00AM (540 minutes).
start_loc = "The Castro"
start_time = 540

# Create the Z3 optimizer
opt = Optimize()

# Decision Variables:
# For each friend i:
#   x[i]    : Bool indicating if the meeting is scheduled.
#   A[i]    : Int representing your arrival time at friend i's location.
#   order[i]: Int representing the meeting order (if scheduled, an integer within 0..num_friends-1, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constrain order variables: if meeting i is scheduled then its order is between 0 and num_friends-1; otherwise, it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure distinct ordering for all scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints.
# For a scheduled meeting, the actual meeting start time is the later of your arrival and the friend’s available start. 
# The meeting must finish (start time + min_duration) before the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any scheduled first meeting (order==0), your arrival time must be at least the start_time plus required travel time from start_loc.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# For any two scheduled meetings i and j, if meeting j directly follows meeting i (order[j] == order[i]+1)
# then the arrival time at the location for meeting j must be at least the departure time from meeting i plus the travel time.
# The departure time from meeting i is defined as max(A[i], avail_start of i) + min_duration of i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        departure_i = If(A[i] < avail_start_i, avail_start_i, A[i]) + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization problem and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Function to convert minutes after midnight to HH:MM format.
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