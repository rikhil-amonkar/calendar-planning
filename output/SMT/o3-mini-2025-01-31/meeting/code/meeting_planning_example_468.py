from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: The Castro, Bayview, Pacific Heights, Alamo Square, Fisherman's Wharf, Golden Gate Park.
travel = {
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,

    ("Bayview", "The Castro"): 20,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,

    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,

    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,

    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,

    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
friends = [
    # Rebecca at Bayview: available 9:00AM (540) to 12:45PM (765), min duration = 90 minutes.
    ("Bayview", 540, 765, 90),
    # Amanda at Pacific Heights: available 6:30PM (1110) to 9:45PM (1305), min duration = 90 minutes.
    ("Pacific Heights", 1110, 1305, 90),
    # James at Alamo Square: available 9:45AM (585) to 9:15PM (1275), min duration = 90 minutes.
    ("Alamo Square", 585, 1275, 90),
    # Sarah at Fisherman's Wharf: available 8:00AM (480) to 9:30PM (1290), min duration = 90 minutes.
    ("Fisherman's Wharf", 480, 1290, 90),
    # Melissa at Golden Gate Park: available 9:00AM (540) to 6:45PM (1125), min duration = 90 minutes.
    ("Golden Gate Park", 540, 1125, 90),
]
friend_names = ["Rebecca", "Amanda", "James", "Sarah", "Melissa"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
# You arrive at The Castro at 9:00AM (540 minutes after midnight)
start_loc = "The Castro"
start_time = 540

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean indicating if meeting with friend i is scheduled.
# A[i]: Arrival time at friend i’s location (in minutes after midnight).
# order[i]: Order of the meeting (if scheduled, an integer between 0 and num_friends-1; if not, -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if scheduled then order[i] must be between 0 and num_friends-1, otherwise order[i] == -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure each scheduled meeting has a distinct order.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend that is scheduled, enforce that the meeting can occur within the friend’s available window.
# The meeting start time is the later of your arrival A[i] and the friend’s avail_start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure you have enough travel time from the start.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    t_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive scheduled meetings, if friend j is visited immediately after friend i,
# ensure that travel time from friend i's location to friend j's location is respected.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        t_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + t_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Gather scheduled meetings with their order.
    scheduled = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            scheduled.append((model.evaluate(order[i]).as_long(), i))
    scheduled.sort()
    
    def to_time(t):
        h = t // 60
        m = t % 60
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