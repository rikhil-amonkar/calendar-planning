from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Locations: Bayview, North Beach, Fisherman's Wharf, Haight-Ashbury, Nob Hill, Golden Gate Park,
# Union Square, Alamo Square, Presidio, Chinatown, Pacific Heights.
travel = {
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Pacific Heights"): 23,
    
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Union Square"): 15,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is represented as a tuple:
#   (location, avail_start, avail_end, min_duration)
# Times are in minutes after midnight.
# You start at Bayview at 9:00 AM (540 minutes)
friends = [
    ("North Beach", 780, 1140, 90),       # Brian: 1:00PM - 7:00PM, 90 minutes.
    ("Fisherman's Wharf", 660, 765, 60),    # Richard: 11:00AM - 12:45PM, 60 minutes.
    ("Haight-Ashbury", 900, 1230, 90),      # Ashley: 3:00PM - 8:30PM, 90 minutes.
    ("Nob Hill", 705, 1110, 75),            # Elizabeth: 11:45AM - 6:30PM, 75 minutes.
    ("Golden Gate Park", 1200, 1305, 105),   # Jessica: 8:00PM - 9:45PM, 105 minutes.
    ("Union Square", 1050, 1320, 60),       # Deborah: 5:30PM - 10:00PM, 60 minutes.
    ("Alamo Square", 1050, 1275, 45),       # Kimberly: 5:30PM - 9:15PM, 45 minutes.
    ("Presidio", 495, 540, 15),             # Matthew: 8:15AM - 9:00AM, 15 minutes.
    ("Chinatown", 825, 1170, 105),          # Kenneth: 1:45PM - 7:30PM, 105 minutes.
    ("Pacific Heights", 855, 960, 30),      # Anthony: 2:15PM - 4:00PM, 30 minutes.
]
friend_names = ["Brian", "Richard", "Ashley", "Elizabeth", "Jessica",
                "Deborah", "Kimberly", "Matthew", "Kenneth", "Anthony"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Bayview"
start_time = 540  # 9:00 AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean (True if meeting friend i is scheduled).
# A[i]: Integer (arrival time at friend i's location, in minutes after midnight).
# order[i]: Integer (the order in which friend i is visited; if scheduled, value in 0..num_friends-1, else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled then order[i] is in valid range, else it is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    opt.add(A[i] >= 0)

# Ensure that no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# For each scheduled meeting, enforce meeting window constraints.
# The meeting actually starts at the later of the arrival time A[i] and the friend’s available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_duration = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_duration <= avail_end))

# For the first scheduled meeting (order == 0), account for travel from the starting location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# For consecutive scheduled meetings, ensure enough travel time is allowed.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, duration_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + duration_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        # If friend j follows friend i in the order, enforce travel time constraint.
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with their order.
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