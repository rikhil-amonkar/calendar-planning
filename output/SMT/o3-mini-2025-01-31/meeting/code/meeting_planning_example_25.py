from z3 import Optimize, Int, Bool, If, And, Or, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes)
travel = {
    ("Golden Gate Park", "Chinatown"): 23,
    ("Chinatown", "Golden Gate Park"): 23,
}

# ----------------------------------------------------------------------------
# Friend data.
# Each friend is a tuple: (location, avail_start, avail_end, min_duration)
# All times are in minutes after midnight.
# You start at Golden Gate Park at 9:00AM (540 minutes).
friends = [
    # 0: David at Chinatown: 4:00PM to 9:45PM (960 to 1305), minimum 105 minutes.
    ("Chinatown", 960, 1305, 105),
]
friend_names = ["David"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Golden Gate Park"
start_time = 540  # 9:00AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables: 
# x[i]: True if meeting friend i is scheduled.
# A[i]: Arrival time at friend i's location.
# order[i]: Order in which friend i is visited. For a single friend, if scheduled, order will be 0.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]
order = [Int(f"order_{i}") for i in range(num_friends)]

# For each friend, if meeting is scheduled, enforce that the order is 0; otherwise, order is -1.
for i in range(num_friends):
    opt.add(If(x[i],
               order[i] == 0,
               order[i] == -1))
    opt.add(A[i] >= 0)

# ----------------------------------------------------------------------------
# Meeting window constraints.
# For scheduled meeting with friend i, the meeting starts at the later of your arrival and the friend's available start.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Travel constraint from the starting location.
# If meeting friend i first (here the only meeting), then the arrival time A[i] must be at least
# your start_time plus the travel time from start_loc to the friend's location.
for i in range(num_friends):
    loc, _, _, _ = friends[i]
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), order[i] != 0, A[i] >= start_time + travel_time))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings.
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
    for i in range(num_friends):
        if model.evaluate(x[i]):
            loc, avail_start, avail_end, dur = friends[i]
            arrival = model.evaluate(A[i]).as_long()
            meeting_start = arrival if arrival >= avail_start else avail_start
            meeting_end = meeting_start + dur
            print(f"Meet {friend_names[i]} at {loc}")
            print(f"  Arrival Time: {to_time(arrival)}")
            print(f"  Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
            
    total = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total)
else:
    print("No feasible schedule found.")