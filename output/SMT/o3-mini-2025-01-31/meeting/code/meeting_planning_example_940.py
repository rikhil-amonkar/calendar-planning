from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Union Square, Mission District, Fisherman's Wharf, Russian Hill,
# Marina District, North Beach, Chinatown, Pacific Heights, The Castro, Nob Hill,
# Sunset District.
travel = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,

    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Sunset District"): 24,

    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,

    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,

    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,

    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,

    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,

    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Sunset District"): 21,

    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,

    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 24,

    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# Starting point is Union Square at 9:00AM (540 minutes).
# Friend details:
# Kevin: Mission District, 8:45PM to 9:45PM, min 60 minutes.
# Mark: Fisherman's Wharf, 5:15PM to 8:00PM, min 90 minutes.
# Jessica: Russian Hill, 9:00AM to 3:00PM, min 120 minutes.
# Jason: Marina District, 3:15PM to 9:45PM, min 120 minutes.
# John: North Beach, 9:45AM to 6:00PM, min 15 minutes.
# Karen: Chinatown, 4:45PM to 7:00PM, min 75 minutes.
# Sarah: Pacific Heights, 5:30PM to 6:15PM, min 45 minutes.
# Amanda: The Castro, 8:00PM to 9:15PM, min 60 minutes.
# Nancy: Nob Hill, 9:45AM to 1:00PM, min 45 minutes.
# Rebecca: Sunset District, 8:45AM to 3:00PM, min 75 minutes.
friends = [
    ("Mission District", 1245, 1305, 60),    # Kevin (8:45PM=1245, 9:45PM=1305)
    ("Fisherman's Wharf", 1035, 1200, 90),     # Mark (5:15PM=1035, 8:00PM=1200)
    ("Russian Hill", 540, 900, 120),           # Jessica (9:00AM=540, 3:00PM=900)
    ("Marina District", 915, 1305, 120),        # Jason (3:15PM=915, 9:45PM=1305)
    ("North Beach", 585, 1080, 15),             # John (9:45AM=585, 6:00PM=1080)
    ("Chinatown", 1005, 1140, 75),              # Karen (4:45PM=1005, 7:00PM=1140)
    ("Pacific Heights", 1050, 1095, 45),        # Sarah (5:30PM=1050, 6:15PM=1095)
    ("The Castro", 1200, 1275, 60),             # Amanda (8:00PM=1200, 9:15PM=1275)
    ("Nob Hill", 585, 780, 45),                 # Nancy (9:45AM=585, 1:00PM=780)
    ("Sunset District", 525, 900, 75),          # Rebecca (8:45AM=525, 3:00PM=900)
]
friend_names = ["Kevin", "Mark", "Jessica", "Jason", "John", "Karen", "Sarah", "Amanda", "Nancy", "Rebecca"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Union Square"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] is a Boolean: True if friend i's meeting is scheduled.
# A[i] is an Int: the arrival time at friend i's location.
# order[i] is an Int: the order in which friend i is visited (0..num_friends-1 if scheduled, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled, assign an order between 0 and num_friends-1; if not, order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that two scheduled meetings do not share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, enforce the time window constraints.
# The meeting starts at the later of your arrival time A[i] and the friend’s avail_start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), ensure sufficient travel time from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings, if friend j is immediately after friend i, account for travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of friends met.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with order number.
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