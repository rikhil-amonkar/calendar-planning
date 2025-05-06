from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between neighborhoods.
# Locations: Embarcadero, Richmond District, Union Square, Financial District,
# Pacific Heights, Nob Hill, Bayview.
travel = {
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 26,
    
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Bayview"): 19,
    
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple:
# (location, avail_start, avail_end, min_duration)
#
# Kenneth:   at Richmond District from 9:15PM to 10:00PM 
#            => [1275, 1320], min_duration = 30.
# Lisa:      at Union Square from 9:00AM to 4:30PM 
#            => [540, 990], min_duration = 45.
# Joshua:    at Financial District from 12:00PM to 3:15PM 
#            => [720, 915], min_duration = 15.
# Nancy:     at Pacific Heights from 8:00AM to 11:30AM 
#            => [480, 690], min_duration = 90.
# Andrew:    at Nob Hill from 11:30AM to 8:15PM 
#            => [690, 1215], min_duration = 60.
# John:      at Bayview from 4:45PM to 9:30PM 
#            => [1005, 1290], min_duration = 75.
friends = [
    ("Richmond District", 1275, 1320, 30),  # Kenneth
    ("Union Square",       540,  990, 45),    # Lisa
    ("Financial District", 720,  915, 15),    # Joshua
    ("Pacific Heights",    480,  690, 90),    # Nancy
    ("Nob Hill",           690, 1215, 60),    # Andrew
    ("Bayview",           1005, 1290, 75),    # John
]
friend_names = ["Kenneth", "Lisa", "Joshua", "Nancy", "Andrew", "John"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Embarcadero"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create Z3 optimizer.
opt = Optimize()

# Decision Variables:
# x[i]: Bool indicating if meeting with friend i is scheduled.
# A[i]: Int representing the arrival time at friend i's location.
# order[i]: Int representing the order (position) of the meeting if scheduled, else -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order is between 0 and (num_friends-1), else set order[i] = -1.
for i in range(num_friends):
    opt.add(
        If(x[i],
           And(order[i] >= 0, order[i] < num_friends),
           order[i] == -1)
    )
    opt.add(A[i] >= 0)

# Ensure each scheduled meeting has a unique order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, ensure that the meeting (starting at the later of arrival time or avail_start)
# finishes before the friend’s availability ends.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure sufficient travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive meetings, enforce that travel time is respected.
# If meeting j immediately follows meeting i then:
# A[j] >= (meeting_i_start + duration_i) + travel_time from friend i's location to friend j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect and sort scheduled meetings by their order.
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