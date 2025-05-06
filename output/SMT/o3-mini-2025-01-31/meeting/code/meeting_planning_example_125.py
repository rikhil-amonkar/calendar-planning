from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations:
travel = {
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Alamo Square"): 17,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Financial District"): 17,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You arrive at Embarcadero at 9:00AM (540 minutes).
friends = [
    # 0: Stephanie at Financial District: Avail from 8:15AM (495) to 11:30AM (690), min meeting 90 minutes.
    ("Financial District", 495, 690, 90),
    # 1: John at Alamo Square: Avail from 10:15AM (615) to 8:45PM (1245), min meeting 30 minutes.
    ("Alamo Square", 615, 1245, 30),
]
friend_names = ["Stephanie", "John"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Embarcadero"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean variable which is True if meeting friend i is scheduled.
# A[i] is an Int variable representing your arrival time at friend i's location.
# order[i] is an Int variable representing the order in which friend i is visited.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if the meeting is scheduled then order[i] is in [0, num_friends-1],
# otherwise fix order[i] to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Arrival times must be non-negative.
    opt.add(A[i] >= 0)

# No two scheduled meetings may have the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For each meeting, the meeting starts at the later of your arrival (A[i]) and the friend's avail_start.
# Then the meeting (which lasts at least min_duration) must finish by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the start location.
# For the first meeting (order[i] == 0) set the arrival time given travel from Embarcadero.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If meeting j immediately follows meeting i (order[j] == order[i] + 1),
# ensure that your arrival time at j is at least the departure time from i (meeting_start_i + meeting duration)
# plus travel time from friend i's location to friend j's location.
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
# Solve the schedule.
if opt.check() == sat:
    model = opt.model()
    
    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"
    
    print("Optimal meeting schedule:")
    # Gather scheduled meetings and sort them by order.
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