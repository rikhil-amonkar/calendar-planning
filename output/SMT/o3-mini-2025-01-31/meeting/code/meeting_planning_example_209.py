from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    # From Sunset District
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    
    # From Chinatown
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    
    # From Russian Hill
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    
    # From North Beach
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
}

# ----------------------------------------------------------------------------
# Friend meeting data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight.
# You arrive at Sunset District at 9:00AM (540 minutes).
friends = [
    # 0: Anthony at Chinatown: available 1:15PM to 2:30PM (795 to 870), min meeting 60 minutes.
    ("Chinatown", 795, 870, 60),
    # 1: Rebecca at Russian Hill: available 7:30PM to 9:15PM (1170 to 1275), min meeting 105 minutes.
    ("Russian Hill", 1170, 1275, 105),
    # 2: Melissa at North Beach: available 8:15AM to 1:30PM (495 to 810), min meeting 105 minutes.
    ("North Beach", 495, 810, 105),
]
friend_names = ["Anthony", "Rebecca", "Melissa"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Sunset District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# x[i] : Bool, True if meeting friend i is scheduled.
# A[i] : Int, representing your arrival time at friend i's location.
# order[i] : Int, the order in which friend i is visited (if meeting scheduled).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting i is scheduled then order[i] is in [0, num_friends-1];
# otherwise we set order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For a scheduled meeting, the meeting actually starts at the later of arrival A[i] or avail_start.
# The meeting must finish by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # meeting must finish by avail_end: meeting_start + duration <= avail_end.
    opt.add(Or(Not(x[i]), meeting_start + duration <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location.
# For a meeting that is first in the order (order[i] == 0), your arrival time must be at or after
# start_time plus the travel time from start_loc to that meeting's location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If meeting j immediately follows meeting i (order[j] == order[i] + 1),
# then your arrival time at meeting j must be no earlier than the departure time from meeting i
# plus the travel time between the corresponding locations.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        loc_j, _, _, _ = friends[j]
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"
    
    print("Optimal meeting schedule:")
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting starts at the later of your arrival time and the friend’s available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")