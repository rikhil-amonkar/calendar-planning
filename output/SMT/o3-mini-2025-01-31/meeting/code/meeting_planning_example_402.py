from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,

    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 17,

    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,

    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,

    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight.
# You arrive at Golden Gate Park at 9:00AM (540 minutes).
friends = [
    # 0: Sarah at Haight-Ashbury: 5:00PM to 9:30PM (1020 to 1290), minimum 105 minutes.
    ("Haight-Ashbury", 1020, 1290, 105),
    # 1: Patricia at Sunset District: 5:00PM to 7:45PM (1020 to 1185), minimum 45 minutes.
    ("Sunset District", 1020, 1185, 45),
    # 2: Matthew at Marina District: 9:15AM to 12:00PM (555 to 720), minimum 15 minutes.
    ("Marina District", 555, 720, 15),
    # 3: Joseph at Financial District: 2:15PM to 6:45PM (855 to 1125), minimum 30 minutes.
    ("Financial District", 855, 1125, 30),
    # 4: Robert at Union Square: 10:15AM to 9:45PM (615 to 1305), minimum 15 minutes.
    ("Union Square", 615, 1305, 15),
]
friend_names = ["Sarah", "Patricia", "Matthew", "Joseph", "Robert"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Golden Gate Park"
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

# For each friend, if the meeting is scheduled then order[i] should be in the range [0, num_friends-1],
# otherwise, we fix order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# No two scheduled meetings can share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For a scheduled meeting with friend i, the meeting starts at the later of your arrival (A[i]) and the friend's available start,
# and then must last at least the required duration (min_duration) within the friend’s available window.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the start location.
# For the first scheduled meeting (order[i] == 0), ensure that you arrive after leaving Golden Gate Park,
# accounting for the travel time from Golden Gate Park to friend i's location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# For any two scheduled meetings i and j where j immediately follows i (order[j] = order[i] + 1),
# ensure that your arrival time at j is after the departure time from i (meeting_start_i + min_dur_i)
# plus the travel time from friend i's location to friend j's location.
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
    # Collect scheduled meetings and sort them by order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting starts at the later of arrival and the available start time.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"     Arrival Time: {to_time(arrival)}")
        print(f"     Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
        
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")