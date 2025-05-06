from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Sunset District, Alamo Square, Russian Hill, Presidio, Financial District.
travel = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,

    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,

    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,

    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Your starting location: Sunset District at 9:00AM (540 minutes)
#
# Kevin: Alamo Square, 8:15AM to 9:30PM  => 495 to 1290, min 75 minutes.
# Kimberly: Russian Hill, 8:45AM to 12:30PM  => 525 to 750, min 30 minutes.
# Joseph: Presidio, 6:30PM to 7:15PM          => 1110 to 1155, min 45 minutes.
# Thomas: Financial District, 7:00PM to 9:45PM  => 1140 to 1305, min 45 minutes.
friends = [
    ("Alamo Square", 495, 1290, 75),    # Kevin
    ("Russian Hill", 525, 750, 30),       # Kimberly
    ("Presidio", 1110, 1155, 45),         # Joseph
    ("Financial District", 1140, 1305, 45) # Thomas
]
friend_names = ["Kevin", "Kimberly", "Joseph", "Thomas"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Sunset District"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean variable indicating whether to schedule a meeting with friend i.
# A[i]: Integer variable for your arrival time at friend i's location.
# order[i]: Integer variable indicating the order in which friend i is visited (if scheduled, value in 0..num_friends-1; otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order[i] must be in [0, num_friends-1], otherwise order[i] is forced to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Enforce that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, enforce the meeting window constraints.
# The meeting actually starts at the later of your arrival time and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure you have enough travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings: if friend j is visited immediately after friend i then ensure enough travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        # You depart friend i after meeting starts (which is max(A[i], avail_start_i)) and lasts dur_i minutes.
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")