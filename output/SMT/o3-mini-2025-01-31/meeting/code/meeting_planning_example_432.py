from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between neighborhoods.
# Neighborhoods: Golden Gate Park, Fisherman's Wharf, Bayview, Mission District,
# Embarcadero, Financial District.
travel = {
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,

    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,

    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Financial District"): 19,

    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 17,

    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,

    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are minutes after midnight.
# Joseph:   Fisherman's Wharf,  available 8:00AM (480) to 5:30PM (1050), min_duration = 90.
# Jeffrey:  Bayview,            available 5:30PM (1050) to 9:30PM (1290), min_duration = 60.
# Kevin:    Mission District,   available 11:15AM (675) to 3:15PM (915), min_duration = 30.
# David:    Embarcadero,        available 8:15AM (495) to 9:00AM (540), min_duration = 30.
# Barbara:  Financial District, available 10:30AM (630) to 4:30PM (990), min_duration = 15.
friends = [
    ("Fisherman's Wharf", 480, 1050, 90),   # Joseph
    ("Bayview",           1050, 1290, 60),    # Jeffrey
    ("Mission District",  675, 915, 30),      # Kevin
    ("Embarcadero",       495, 540, 30),       # David
    ("Financial District",630, 990, 15),       # Barbara
]
friend_names = ["Joseph", "Jeffrey", "Kevin", "David", "Barbara"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Golden Gate Park"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i] : Boolean indicating if meeting with friend i is scheduled.
#   A[i] : Integer representing your arrival time at friend i’s location (minutes after midnight).
#   order[i] : Integer representing the visitation order if scheduled (0 through num_friends-1), else -1.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If meeting i is scheduled then order must be in [0, num_friends-1], otherwise order = -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure every scheduled meeting gets a distinct order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, the meeting will start at the later of your arrival and the friend's available start.
# Then the meeting lasts at least the minimum duration and must finish by the available end.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure you allow enough travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    tt = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + tt))

# For any pair of consecutive scheduled meetings: if friend j is visited immediately after friend i,
# then your arrival at j must be at least the departure time of i (i.e. meeting start plus duration)
# plus the travel time from friend i's location to friend j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i  # meeting i end time
        travel_ij = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + travel_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and print the schedule.
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings and sort them by their order.
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
        arr_time = model.evaluate(A[i]).as_long()
        meeting_start = arr_time if arr_time >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arr_time)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
        
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")