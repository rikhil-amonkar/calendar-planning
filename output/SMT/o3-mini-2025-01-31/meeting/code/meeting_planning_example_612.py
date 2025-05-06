from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,
    
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
}

# Define friend meeting details.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Arriving at Alamo Square is 9:00AM = 540.
friends = [
    # Emily: at Russian Hill from 12:15PM (735) to 2:15PM (855); meeting >= 105 minutes.
    ("Russian Hill", 735, 855, 105),
    # Mark: at Presidio from 2:45PM (885) to 7:30PM (1170); meeting >= 60 minutes.
    ("Presidio", 885, 1170, 60),
    # Deborah: at Chinatown from 7:30AM (450) to 3:30PM (930); meeting >= 45 minutes.
    ("Chinatown", 450, 930, 45),
    # Margaret: at Sunset District from 9:30PM (1290) to 10:30PM (1350); meeting >= 60 minutes.
    ("Sunset District", 1290, 1350, 60),
    # George: at The Castro from 7:30AM (450) to 2:15PM (855); meeting >= 60 minutes.
    ("The Castro", 450, 855, 60),
    # Andrew: at Embarcadero from 8:15PM (1215) to 10:00PM (1320); meeting >= 75 minutes.
    ("Embarcadero", 1215, 1320, 75),
    # Steven: at Golden Gate Park from 11:15AM (675) to 9:15PM (1275); meeting >= 105 minutes.
    ("Golden Gate Park", 675, 1275, 105)
]
friend_names = ["Emily", "Mark", "Deborah", "Margaret", "George", "Andrew", "Steven"]
num_friends = len(friends)

# Starting conditions:
start_loc = "Alamo Square"
start_time = 540  # 9:00AM

# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
# For each friend i:
#   x[i]    : Bool indicating if meeting i is scheduled.
#   A[i]    : The arrival time at friend i's location (in minutes after midnight).
#   order[i]: The order (position) of the meeting (if scheduled) in the itinerary; otherwise -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, its order is between 0 and num_friends-1. If not, its order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure all scheduled meetings have distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# If meeting i is scheduled, then the meeting starts at the later of your arrival A[i] and the friend’s available start.
# The meeting must finish (start + min_duration) by the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any scheduled meeting that is first (order == 0), your arrival time must be at least
# the start_time plus the travel time from the start location (Alamo Square) to that friend's location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# For any two scheduled meetings i and j, if meeting j immediately follows meeting i (order[j] == order[i] + 1),
# then your arrival time at meeting j must be at least the departure time from meeting i plus travel time.
# The departure time from meeting i is defined as max(A[i], avail_start_i) + min_duration_i.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization problem and print the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings and sort them by their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Helper function to convert minutes to HH:MM format.
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