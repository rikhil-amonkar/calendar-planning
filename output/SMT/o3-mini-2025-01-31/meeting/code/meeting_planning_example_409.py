from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Fisherman's Wharf, Bayview, Golden Gate Park, Nob Hill, Marina District, Embarcadero.
travel = {
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 25,
    ("Bayview", "Embarcadero"): 19,
    
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is modeled as a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times are expressed in minutes after midnight.
#
# Starting point: Fisherman's Wharf at 9:00 AM (540 minutes)
# Thomas: Bayview, available 3:30PM to 6:30PM (930 to 1110), min = 120 minutes.
# Stephanie: Golden Gate Park, available 6:30PM to 9:45PM (1110 to 1185), min = 30 minutes.
# Laura: Nob Hill, available 8:45AM to 4:15PM (525 to 975), min = 30 minutes.
# Betty: Marina District, available 6:45PM to 9:45PM (1125 to 1185), min = 45 minutes.
# Patricia: Embarcadero, available 5:30PM to 10:00PM (1050 to 1320), min = 45 minutes.
friends = [
    ("Bayview", 930, 1110, 120),        # Thomas
    ("Golden Gate Park", 1110, 1185, 30), # Stephanie
    ("Nob Hill", 525, 975, 30),           # Laura
    ("Marina District", 1125, 1185, 45),  # Betty
    ("Embarcadero", 1050, 1320, 45)        # Patricia
]
friend_names = ["Thomas", "Stephanie", "Laura", "Betty", "Patricia"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Fisherman's Wharf"
start_time = 540  # 9:00 AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean, True if meeting friend i is scheduled.
# A[i]: Integer, arrival time at friend i's location.
# order[i]: Integer, order in which friend i is visited (if scheduled, value from 0 to num_friends-1; else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# Constraint: If a meeting is scheduled, set its order in valid range; otherwise, force order == -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# Meeting time constraints:
# The meeting start time is the later of arrival time A[i] and the friend’s available start time.
for i in range(num_friends):
    loc, avail_start, avail_end, duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + duration <= avail_end))

# Travel constraint from the starting location for the first scheduled meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# Travel constraints between consecutive meetings.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, duration_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + duration_i
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

    # Gather scheduled meetings along with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()

    def to_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"

    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
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