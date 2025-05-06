from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes)
# From Alamo Square to Richmond District: 12.
# From Richmond District to Alamo Square: 13.
travel = {
    ("Alamo Square", "Richmond District"): 12,
    ("Richmond District", "Alamo Square"): 13,
}

# ----------------------------------------------------------------------------
# Friend data.
# Only one friend, Timothy:
# - Location: Richmond District
# - Available from 8:45PM (1245 minutes) to 9:30PM (1290 minutes)
# - Minimum meeting duration: 45 minutes
friends = [
    ("Richmond District", 1245, 1290, 45)  # Timothy
]
friend_names = ["Timothy"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
# You arrive at Alamo Square at 9:00AM (540 minutes after midnight)
start_loc = "Alamo Square"
start_time = 540

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean that indicates whether the meeting with friend i is scheduled.
# A[i]: Integer representing your arrival time at friend i's location.
# order[i]: Integer representing the visitation order.
#          If the meeting is scheduled, order[i] is in [0, num_friends-1], otherwise order[i] = -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constraints on order: if meeting is scheduled, then order in [0, num_friends-1], else order = -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# For scheduled meetings, ensure distinct order numbers.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, the meeting begins at the later of your arrival (A[i]) or the friend's available start.
# The meeting must last at least the minimum duration and finish by the available end time.
for i in range(num_friends):
    loc, avail_start, avail_end, duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + duration <= avail_end))

# For the first scheduled meeting (order == 0), ensure that there is enough travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    if (start_loc, loc) in travel:
        travel_time = travel[(start_loc, loc)]
    else:
        travel_time = 0  # fallback in case travel is not defined
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# (Note: In this problem we only have one friend so there is no consecutive meeting constraint.)

# ----------------------------------------------------------------------------
# Objective: Maximize the total number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print the results.
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings sorted by their order.
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
        loc, avail_start, avail_end, duration = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + duration
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")