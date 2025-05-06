from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, Sum

# ----------------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Each key is a tuple (origin, destination).
travel = {
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Nob Hill"): 16,
    
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Nob Hill"): 27,
    
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Haight-Ashbury"): 13,
}

# ----------------------------------------------------------------------------
# Friends data.
# Each friend is defined as a tuple:
#   (location, avail_start, avail_end, min_duration)
# All times are in minutes after midnight.
# You start at Russian Hill at 9:00AM (540).
friends = [
    # 0: Mark at Marina District: 6:45PM to 9:00PM (1125 to 1260), min 90 minutes.
    ("Marina District", 1125, 1260, 90),
    # 1: Karen at Financial District: 9:30AM to 12:45PM (570 to 765), min 90 minutes.
    ("Financial District", 570, 765, 90),
    # 2: Barbara at Alamo Square: 10:00AM to 7:30PM (600 to 1170), min 90 minutes.
    ("Alamo Square", 600, 1170, 90),
    # 3: Nancy at Golden Gate Park: 4:45PM to 8:00PM (1005 to 1200), min 105 minutes.
    ("Golden Gate Park", 1005, 1200, 105),
    # 4: David at The Castro: 9:00AM to 6:00PM (540 to 1080), min 120 minutes.
    ("The Castro", 540, 1080, 120),
    # 5: Linda at Bayview: 6:15PM to 7:45PM (1095 to 1185), min 45 minutes.
    ("Bayview", 1095, 1185, 45),
    # 6: Kevin at Sunset District: 10:00AM to 5:45PM (600 to 1065), min 120 minutes.
    ("Sunset District", 600, 1065, 120),
    # 7: Matthew at Haight-Ashbury: 10:15AM to 3:30PM (615 to 930), min 45 minutes.
    ("Haight-Ashbury", 615, 930, 45),
    # 8: Andrew at Nob Hill: 11:45AM to 4:45PM (705 to 1005), min 105 minutes.
    ("Nob Hill", 705, 1005, 105),
]
friend_names = ["Mark", "Karen", "Barbara", "Nancy", "David", "Linda", "Kevin", "Matthew", "Andrew"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Russian Hill"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i]: Boolean variable, True if meeting friend i is scheduled.
# A[i]: Arrival time (in minutes after midnight) at friend i's location.
# order[i]: Order in which friend i is visited (if scheduled, value between 0 and num_friends - 1; else -1).
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# If a meeting is scheduled then order should be between 0 and num_friends - 1, otherwise fix order to -1.
for i in range(num_friends):
    opt.add(If(x[i],
               And(order[i] >= 0, order[i] < num_friends),
               order[i] == -1))
    # Arrival times must be nonnegative.
    opt.add(A[i] >= 0)

# Ensure no two scheduled meetings share the same order.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Or(Not(x[i]), Not(x[j]), order[i] != order[j]))

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For each scheduled meeting, the meeting starts at the later of your arrival time and the friend’s available start;
# the meeting must finish (start + minimum duration) by the available end.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location for the first scheduled meeting.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Travel constraints between consecutive meetings.
# If friend j is visited immediately after friend i, then
# your arrival time at j must be at least the departure time from i (meeting start + meeting duration)
# plus the travel time from i's location to j's location.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i, avail_start_i, _, dur_i = friends[i]
        loc_j, avail_start_j, _, _ = friends[j]
        meeting_start_i = If(A[i] < avail_start_i, avail_start_i, A[i])
        departure_time_i = meeting_start_i + dur_i
        travel_time_ij = travel.get((loc_i, loc_j), 0)
        cond = And(x[i], x[j], order[j] == order[i] + 1)
        opt.add(Or(Not(cond), A[j] >= departure_time_i + travel_time_ij))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve and output the schedule.
if opt.check() == sat:
    model = opt.model()
    # Collect all scheduled meetings along with their order.
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            schedule.append((model.evaluate(order[i]).as_long(), i))
    schedule.sort()
    
    def to_time(t):
        hrs = t // 60
        mins = t % 60
        return f"{hrs:02d}:{mins:02d}"
    
    print("Optimal meeting schedule:")
    for ord_val, i in schedule:
        loc, avail_start, avail_end, dur = friends[i]
        arrival = model.evaluate(A[i]).as_long()
        # The meeting begins at the later of the arrival and the friend's available start.
        meeting_start = arrival if arrival >= avail_start else avail_start
        meeting_end = meeting_start + dur
        print(f" Order {ord_val}: Meet {friend_names[i]} at {loc}")
        print(f"    Arrival Time: {to_time(arrival)}")
        print(f"    Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")