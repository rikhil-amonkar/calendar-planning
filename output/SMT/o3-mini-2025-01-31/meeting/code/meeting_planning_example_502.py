from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# --------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Each key is a tuple (From, To) with the travel time from From -> To.
travel = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,
    
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,
    
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
}

# --------------------------------------------------------------------
# Friend meeting details.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
#
# Stephanie: at Golden Gate Park from 11:00AM to 3:00PM, meeting >= 105 minutes.
# Karen:     at Chinatown from 1:45PM to 4:30PM, meeting >= 15 minutes.
# Brian:     at Union Square from 3:00PM to 5:15PM, meeting >= 30 minutes.
# Rebecca:   at Fisherman's Wharf from 8:00AM to 11:15AM, meeting >= 30 minutes.
# Joseph:    at Pacific Heights from 8:15AM to 9:30AM, meeting >= 60 minutes.
# Steven:    at North Beach from 2:30PM to 8:45PM, meeting >= 120 minutes.
friends = [
    ("Golden Gate Park", 660, 900, 105),  # Stephanie: 11:00AM (660) to 3:00PM (900)
    ("Chinatown",       825, 990, 15),     # Karen:     1:45PM (825) to 4:30PM (990)
    ("Union Square",    900, 1035, 30),     # Brian:     3:00PM (900) to 5:15PM (1035)
    ("Fisherman's Wharf",480, 675, 30),     # Rebecca:   8:00AM (480) to 11:15AM (675)
    ("Pacific Heights", 495, 570, 60),      # Joseph:    8:15AM (495) to 9:30AM (570)
    ("North Beach",     870, 1245, 120)     # Steven:    2:30PM (870) to 8:45PM (1245)
]
friend_names = ["Stephanie", "Karen", "Brian", "Rebecca", "Joseph", "Steven"]
num_friends = len(friends)

# --------------------------------------------------------------------
# Starting location and time.
start_loc = "Financial District"
start_time = 540  # 9:00 AM

# --------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# For each friend i:
#   x[i]    : Bool, True if meeting with friend i is scheduled.
#   A[i]    : Int, arrival time (in minutes after midnight) at friend i's location.
#   order[i]: Int, the order index for friend i if scheduled; otherwise fixed to -1.
x     = [Bool(f"x_{i}") for i in range(num_friends)]
A     = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# --------------------------------------------------------------------
# Enforce that if a meeting is scheduled, an order between 0 and num_friends-1 is assigned;
# if not scheduled, then order[i] is fixed to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Enforce that scheduled meetings receive distinct order values.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each friend, if scheduled, ensure the meeting fits within the available window.
# The meeting is assumed to start at the later of your arrival time and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + dur <= avail_end))

# For the first scheduled meeting (order == 0), you travel from the start location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    # Travel time from starting location (Financial District) to friend i's location.
    t_time = travel[(start_loc, loc)]
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + t_time))

# For consecutive meetings:
# If friend j immediately follows friend i (order[j] == order[i] + 1), then
# your arrival at friend j must be at least the departure time from friend i plus travel time.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_i = meeting_start_i + dur_i
        t_time = travel[(loc_i, loc_j)]
        condition = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(condition), A[j] >= departure_i + t_time))

# --------------------------------------------------------------------
# Objective: Maximize total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# --------------------------------------------------------------------
# Solve and print the optimal meeting schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()  # sort by order
    def to_time(minutes):
        hr = minutes // 60
        mn = minutes % 60
        return f"{hr:02d}:{mn:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        start_meet = arrival if arrival >= avail_start else avail_start
        end_meet = start_meet + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival time: {to_time(arrival)}")
        print(f"    Meeting from: {to_time(start_meet)} to {to_time(end_meet)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")