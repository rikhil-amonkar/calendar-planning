from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, sat

# Define directional travel times (in minutes) between locations.
travel = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18
}

# Define friend meeting information.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Betty: at Presidio from 10:15AM (615) to 9:30PM (1290); meeting >= 45 minutes.
    ("Presidio", 615, 1290, 45),
    # David: at Richmond District from 1:00PM (780) to 8:15PM (1215); meeting >= 90 minutes.
    ("Richmond District", 780, 1215, 90),
    # Barbara: at Fisherman's Wharf from 9:15AM (555) to 8:15PM (1215); meeting >= 120 minutes.
    ("Fisherman's Wharf", 555, 1215, 120)
]
num_friends = len(friends)

# Starting conditions: 
# You arrive at Embarcadero at 9:00AM = 540 minutes after midnight.
start_loc = "Embarcadero"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# For each friend, create decision variables:
# x[i]: Bool indicating whether to schedule a meeting with friend i.
# A[i]: Integer for the arrival time (in minutes after midnight) at friend i's location.
# order[i]: Integer giving the order (position) in which friend i is met (0 ... num_friends-1)
#           if scheduled; if not scheduled, order[i] is forced to -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If scheduled, order is between 0 and num_friends-1, else it equals -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that scheduled meetings have unique order positions.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, ensure that if a meeting is scheduled then the meeting can start at the later of
# your arrival A[i] and the friend’s availability start, and finish within their availability window.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# Travel constraints:
# For the first meeting in your schedule (order == 0), you come from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings: if friend j follows friend i then you must have enough time to travel.
# We define departure time from friend i as the later of A[i] and avail_start, plus min duration.
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

# The objective: maximize the number of meetings (friends met)
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# Solve and print the resulting schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings and sort them by order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    print("Optimal meeting schedule:")
    
    # Convert minutes to HH:MM string.
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    friend_names = ["Betty", "David", "Barbara"]
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # Meeting cannot start before the friend is available.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from {to_time(meeting_start)} to {to_time(meeting_end)}")
    
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible meeting schedule found.")