from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Embarcadero, Golden Gate Park, Haight-Ashbury, Bayview, Presidio, Financial District.
travel = {
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,

    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,

    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,

    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Financial District"): 19,

    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Financial District"): 23,

    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Presidio"): 22,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Mary:      at Golden Gate Park,      available 8:45AM (525) to 11:45AM (705), min_duration = 45.
# Kevin:     at Haight-Ashbury,        available 10:15AM (615) to 4:15PM (975),  min_duration = 90.
# Deborah:   at Bayview,               available 3:00PM (900) to 7:15PM (1155),  min_duration = 120.
# Stephanie: at Presidio,              available 10:00AM (600) to 5:15PM (1035), min_duration = 120.
# Emily:     at Financial District,    available 11:30AM (690) to 9:45PM (1305), min_duration = 105.
friends = [
    ("Golden Gate Park",   525, 705, 45),    # Mary
    ("Haight-Ashbury",     615, 975, 90),    # Kevin
    ("Bayview",            900, 1155, 120),  # Deborah
    ("Presidio",           600, 1035, 120),  # Stephanie
    ("Financial District", 690, 1305, 105),  # Emily
]
friend_names = ["Mary", "Kevin", "Deborah", "Stephanie", "Emily"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Embarcadero"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i]: Boolean indicating if meeting with friend i is scheduled.
#   A[i]: Integer representing your arrival time (in minutes after midnight) at friend i's location.
#   order[i]: Integer representing the order of meeting (if scheduled between 0 and num_friends-1, otherwise -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, the order must be between 0 and num_friends-1; if not scheduled, order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that each scheduled meeting gets a distinct order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if meeting is scheduled then the meeting starts at the later of your arrival A[i]
# or the friend's available start time; it then lasts the required duration and must finish by avail_end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure enough travel time from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings:
# If friend j is visited immediately after friend i then your arrival at j must be at least the departure time from i
# (meeting start plus duration) plus the travel time from i's location to j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i  # meeting finish time at i
        travel_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_ij))

# ----------------------------------------------------------------------------
# Objective: Maximize the total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather and sort scheduled meetings by visitation order.
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