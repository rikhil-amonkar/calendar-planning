from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Marina District"): 6,
    
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight.
# You arrive at Richmond District at 9:00AM (540 minutes).
friends = [
    # 0: Jessica at Pacific Heights: available 3:30PM to 4:45PM (930 to 1005), minimum meeting time 45 minutes.
    ("Pacific Heights", 930, 1005, 45),
    # 1: Carol at Marina District: available 11:30AM to 3:00PM (690 to 900), minimum meeting time 60 minutes.
    ("Marina District", 690, 900, 60),
]
friend_names = ["Jessica", "Carol"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Richmond District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean variable that's True if meeting friend i is scheduled.
# A[i] is an integer variable representing the arrival time at friend i's location.
# order[i] is an integer representing the meeting order.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, assign an order in the range [0, num_friends-1];
# otherwise, fix the order variable to -1.
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
# For a scheduled meeting, the meeting starts at the later of your arrival (A[i]) 
# and the friend's available start time; then the meeting lasts for the minimum duration.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    # meeting start is the later of A[i] and avail_start.
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    # Meeting must end (start + duration) by avail_end.
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the start location.
# For the first scheduled meeting (order[i] == 0), the arrival time must account for travel
# from the starting location (Richmond District) to the friend’s location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# When meeting j immediately follows meeting i (order[j] == order[i] + 1), ensure that
# your arrival at friend j occurs after you have finished the meeting with friend i and completed travel.
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
    # Collect scheduled meetings sorted by their order.
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