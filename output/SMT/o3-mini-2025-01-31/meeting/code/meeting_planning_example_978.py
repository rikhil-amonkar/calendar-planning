from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    # From Embarcadero
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "The Castro"): 27,
    
    # From Financial District
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "The Castro"): 20,
    
    # From Russian Hill
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    
    # From Marina District
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "The Castro"): 22,
    
    # From Richmond District
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "The Castro"): 16,
    
    # From Pacific Heights
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "The Castro"): 16,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    
    # From Presidio
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "The Castro"): 21,
    
    # From Nob Hill
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "The Castro"): 17,
    
    # From The Castro
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Nob Hill"): 16
}

# Define friend meeting details.
# Each friend is represented as a tuple: 
# (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Stephanie: at Fisherman's Wharf from 3:30PM (930) to 10:00PM (1320); meeting >= 30 minutes.
    ("Fisherman's Wharf", 930, 1320, 30),
    # Lisa: at Financial District from 10:45AM (645) to 5:15PM (1035); meeting >= 15 minutes.
    ("Financial District", 645, 1035, 15),
    # Melissa: at Russian Hill from 5:00PM (1020) to 9:45PM (1305); meeting >= 120 minutes.
    ("Russian Hill", 1020, 1305, 120),
    # Betty: at Marina District from 10:45AM (645) to 2:15PM (855); meeting >= 60 minutes.
    ("Marina District", 645, 855, 60),
    # Sarah: at Richmond District from 4:15PM (975) to 7:30PM (1170); meeting >= 105 minutes.
    ("Richmond District", 975, 1170, 105),
    # Daniel: at Pacific Heights from 6:30PM (1110) to 9:45PM (1305); meeting >= 60 minutes.
    ("Pacific Heights", 1110, 1305, 60),
    # Joshua: at Haight-Ashbury from 9:00AM (540) to 3:30PM (930); meeting >= 15 minutes.
    ("Haight-Ashbury", 540, 930, 15),
    # Joseph: at Presidio from 7:00AM (420) to 1:00PM (780); meeting >= 45 minutes.
    ("Presidio", 420, 780, 45),
    # Andrew: at Nob Hill from 7:45PM (1185) to 10:00PM (1320); meeting >= 105 minutes.
    ("Nob Hill", 1185, 1320, 105),
    # John: at The Castro from 1:15PM (795) to 7:45PM (1185); meeting >= 45 minutes.
    ("The Castro", 795, 1185, 45)
]
friend_names = ["Stephanie", "Lisa", "Melissa", "Betty", "Sarah", "Daniel", "Joshua", "Joseph", "Andrew", "John"]
num_friends = len(friends)

# Starting conditions:
# You arrive at Embarcadero at 9:00AM = 540 minutes after midnight.
start_loc = "Embarcadero"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
# For each friend i:
#   x[i]    : Bool indicating if the meeting is scheduled.
#   A[i]    : Int representing the arrival time at the friend’s location (in minutes after midnight).
#   order[i]: Int representing the meeting order (if scheduled, an integer in [0, num_friends-1]; else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constrain order variable: if a meeting is scheduled then order in [0, num_friends-1], otherwise order == -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure scheduled meetings get distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints.
# If meeting i is scheduled, then its effective start time is max(A[i], avail_start).
# The meeting must finish (start time + min_duration) before avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For each friend i scheduled as the first meeting (order == 0), 
# the arrival time must be at least start_time + travel_time from start_loc.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# Travel constraints between consecutive meetings:
# For any two scheduled meetings i and j, if meeting j immediately follows meeting i (order[j] == order[i] + 1),
# then the arrival time for meeting j must be at least the departure time from meeting i plus travel time.
# Here the departure time from meeting i is defined as: max(A[i], avail_start_i) + min_duration.
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

# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve the optimization problem and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings with their order.
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
        # The effective meeting start is the later of your arrival time and the friend’s available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")