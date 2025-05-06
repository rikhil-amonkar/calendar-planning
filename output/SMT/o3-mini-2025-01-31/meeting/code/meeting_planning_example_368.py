from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Financial District"): 19,
    
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Financial District"): 11,
    
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at Bayview at 9:00AM (540 minutes).
friends = [
    # 0: Joseph at Russian Hill: available 8:30AM to 7:15PM (510 to 1155), min 60 minutes.
    ("Russian Hill", 510, 1155, 60),
    # 1: Nancy at Alamo Square: available 11:00AM to 4:00PM (660 to 960),   min 90 minutes.
    ("Alamo Square", 660, 960, 90),
    # 2: Jason at North Beach: available 4:45PM to 9:45PM (1005 to 1305),      min 15 minutes.
    ("North Beach", 1005, 1305, 15),
    # 3: Jeffrey at Financial District: available 10:30AM to 3:45PM (630 to 945), min 45 minutes.
    ("Financial District", 630, 945, 45),
]
friend_names = ["Joseph", "Nancy", "Jason", "Jeffrey"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Bayview"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean variable which is True if meeting friend i is scheduled.
# A[i] is an integer variable representing the arrival time at friend i's location.
# order[i] is an integer variable representing the order in which friend i is visited.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if the meeting is scheduled then the order is in [0, num_friends-1]; else we fix it to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings have the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For each scheduled meeting, the meeting starts at the later of your arrival and the friend’s available start,
# and the meeting (of required duration) must end no later than the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location.
# For the first scheduled meeting (order[i] == 0), ensure your arrival time includes travel time from Bayview.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If meeting j immediately follows meeting i (order[j] == order[i] + 1), ensure that your arrival at j is after
# the departure time from i (meeting start of i + minimum duration) plus travel time from friend i's location to j's.
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
    # Get the scheduled meetings and sort by their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    for ord_val, i in schedule:
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