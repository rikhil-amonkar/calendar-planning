from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You start at Pacific Heights at 9:00AM (540 minutes).
friends = [
    # 0: Jason at Presidio: available 10:00AM (600) to 4:15PM (975), minimum meeting duration = 90 minutes.
    ("Presidio", 600, 975, 90),
    # 1: Kenneth at Marina District: available 3:30PM (930) to 4:45PM (1005), minimum meeting duration = 45 minutes.
    ("Marina District", 930, 1005, 45),
]
friend_names = ["Jason", "Kenneth"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Pacific Heights"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Bool, True if meeting friend i is scheduled.
# A[i]: Int, arrival time at friend i's location.
# order[i]: Int, represents the order in which friend i is visited (if scheduled).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if the meeting is scheduled, assign an order in [0, num_friends-1];
# otherwise, fix the order to -1. Also, arrival times are nonnegative.
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
# For each scheduled meeting, the meeting starts at the later of your arrival (A[i]) and the friend’s available start.
# Then, the meeting (of duration min_duration) must finish by the friend’s available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the start location.
# For a scheduled meeting that is first in the order (order[i]==0), the arrival time must be at least:
# start_time + travel time from your starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# For any two scheduled meetings where one immediately follows the other (order[j]==order[i]+1),
# ensure that the arrival time to meeting j is at least the departure time from meeting i plus the travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        # Meeting i starts at max(A[i], avail_start_i) and lasts for dur_i minutes.
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
    # Gather scheduled meetings and sort them by their order.
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