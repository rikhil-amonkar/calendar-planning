from z3 import Optimize, Int, Bool, If, And, Or, sat, Sum

# ----------------------------------------------------------------------------
# Travel distances (in minutes)
travel = {
    ("Nob Hill", "Presidio"): 17,
    ("Presidio", "Nob Hill"): 18,
}

# ----------------------------------------------------------------------------
# Friend data.
# Each friend is described as a tuple:
# (location, available start time, available end time, minimum meeting duration)
# All times are in minutes after midnight.
# You arrive at Nob Hill at 9:00AM (540 minutes).
friends = [
    # 0: Robert at Presidio: available from 11:15AM (675) to 5:45PM (1065), with minimum meeting duration 120 minutes.
    ("Presidio", 675, 1065, 120),
]
friend_names = ["Robert"]
num_friends = len(friends)

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Nob Hill"
start_time = 540  # 9:00 AM

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x[i] -> Bool: True if meeting with friend i is scheduled.
# A[i] -> Int: Arrival time at friend i's location.
x = [Bool(f"x_{i}") for i in range(num_friends)]
A = [Int(f"A_{i}") for i in range(num_friends)]

# ----------------------------------------------------------------------------
# Constraints for each friend meeting.
for i in range(num_friends):
    loc, avail_start, avail_end, min_dur = friends[i]
    # The meeting can only happen if it's scheduled.
    # The arrival time at friend’s location must be nonnegative.
    opt.add(A[i] >= 0)
    
    # If meeting is scheduled, ensure travel constraints from the starting location.
    # You travel from Nob Hill to the friend's location.
    travel_time = travel.get((start_loc, loc), 0)
    opt.add(Or(Not(x[i]), A[i] >= start_time + travel_time))
    
    # Define meeting start as the later of the arrival time and the friend’s available start.
    meeting_start = If(A[i] < avail_start, avail_start, A[i])
    
    # The meeting must finish (meeting start + minimum duration) by the friend's available end.
    opt.add(Or(Not(x[i]), meeting_start + min_dur <= avail_end))

# ----------------------------------------------------------------------------
# Objective: maximize the number of meetings scheduled.
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
            loc, avail_start, avail_end, min_dur = friends[i]
            arrival = model.evaluate(A[i]).as_long()
            # The meeting starts at the later of the arrival time and the available start.
            meeting_start = arrival if arrival >= avail_start else avail_start
            meeting_end = meeting_start + min_dur
            print(f"Meet {friend_names[i]} at {loc}")
            print(f"  Arrival Time: {to_time(arrival)}")
            print(f"  Meeting Time: {to_time(meeting_start)} - {to_time(meeting_end)}")
    total_meetings = sum(1 for i in range(num_friends) if model.evaluate(x[i]))
    print("Total friends met:", total_meetings)
else:
    print("No feasible schedule found.")