from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21
}

# Define friend meeting details.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# 9:00AM is 540.
# Emily: at Presidio from 4:15PM (16:15 -> 16*60+15 = 975) to 9:00PM (1260); meeting >= 105 minutes.
# Joseph: at Richmond District from 5:15PM (17:15 -> 17*60+15 = 1035) to 10:00PM (1320); meeting >= 120 minutes.
# Melissa: at Financial District from 3:45PM (15:45 -> 945) to 9:45PM (1305); meeting >= 75 minutes.
friends = [
    ("Presidio", 975, 1260, 105),
    ("Richmond District", 1035, 1320, 120),
    ("Financial District", 945, 1305, 75)
]
friend_names = ["Emily", "Joseph", "Melissa"]
num_friends = len(friends)

# Starting conditions:
# Arriving at Fisherman's Wharf at 9:00AM.
start_loc = "Fisherman's Wharf"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Decision Variables:
# For each friend i:
#   x[i]: Bool indicating if the meeting is scheduled.
#   A[i]: Arrival time at friend i's location.
#   order[i]: The position/order of the meeting if scheduled; otherwise -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constrain order:
# If a meeting is scheduled, its order is between 0 and num_friends-1;
# if not scheduled then order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure all scheduled meetings have distinct orders.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting availability constraints:
# If meeting i is scheduled, then the effective meeting start time is the max of A[i] and the friend’s available start.
# The meeting must finish (start + min_duration) before the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraint for the first meeting:
# For any scheduled meeting that is first (order==0), your arrival time A[i] must be at least (start_time + travel time)
# from the starting location to friend i’s location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Travel constraints between consecutive meetings:
# If meeting j immediately follows meeting i (order[j] == order[i] + 1),
# then arrival time at j (A[j]) must be at least the departure time from meeting i plus travel time.
# Departure time for meeting i is defined as max(A[i], avail_start_i) + min_duration_i.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        travel_time = travel[(loc_i, loc_j)]
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time))

# Objective: Maximize the total number of meetings scheduled.
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
    
    # Helper function to convert minutes to HH:MM.
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    for order_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting starts at the maximum of arrival time and available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {order_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total_meetings = sum([1 for i in range(num_friends) if model.evaluate(x[i])])
    print("Total friends met:", total_meetings)
else:
    print("No feasible meeting schedule found.")