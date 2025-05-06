from z3 import Optimize, Int, Bool, If, And, Or, sat

# ----------------------------------------------------------------------------
# Given travel times (in minutes)
# Russian Hill to Richmond District: 14.
# (The reverse is given as 13, but we only need the travel time from your start.)
travel_time = {("Russian Hill", "Richmond District"): 14}

# ----------------------------------------------------------------------------
# Friend data for Daniel: (location, avail_start, avail_end, min_duration)
# Daniel is at Richmond District from 7:00PM to 8:15PM.
# 7:00PM => 1140 minutes; 8:15PM => 1215 minutes.
# Minimum meeting duration is 75 minutes.
friend = ("Richmond District", 1140, 1215, 75)
friend_name = "Daniel"

# ----------------------------------------------------------------------------
# Starting parameters.
start_loc = "Russian Hill"
start_time = 540  # 9:00AM in minutes after midnight

# ----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x: Boolean, True if meeting with Daniel is scheduled.
# A: Integer, arrival time (in minutes) at Daniel's location.
# order: Integer, the order of the meeting if scheduled (here only one meeting, so order is 0 if scheduled).
x = Bool("x_0")
A = Int("A_0")
order = Int("order_0")

# When meeting is scheduled, order must be within [0,0]; if not scheduled, order is -1.
opt.add(If(x, And(order >= 0, order < 1), order == -1))
opt.add(A >= 0)

# Constraint: For the meeting with Daniel (if scheduled) as the first meeting,
# ensure travel time is met from the starting location.
# Russian Hill to Richmond District takes 14 minutes.
opt.add(Or(Not(x), order != 0, A >= start_time + travel_time[(start_loc, friend[0])]))

# Define the meeting start time as the later of your arrival time (A) or Daniel's available start time.
meeting_start = If(A < friend[1], friend[1], A)

# Constraint: Ensure that the meeting lasts at least the required duration (75 minutes)
# and finishes by Daniel's available end time.
opt.add(Or(Not(x), meeting_start + friend[3] <= friend[2]))

# ----------------------------------------------------------------------------
# Objective: Maximize the number of meetings scheduled.
opt.maximize(If(x, 1, 0))

# ----------------------------------------------------------------------------
# Solve the model and output the schedule.
if opt.check() == sat:
    model = opt.model()
    if model.evaluate(x):
        arrival_time = model.evaluate(A).as_long()
        # The meeting starts at the later of arrival_time and friend[1] (Daniel's start avail time)
        meeting_start_time = friend[1] if arrival_time < friend[1] else arrival_time
        meeting_end_time = meeting_start_time + friend[3]

        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        print("Optimal meeting schedule:")
        print(f"Meet {friend_name} at {friend[0]}")
        print("Arrival Time:", to_time(arrival_time))
        print("Meeting Time:", to_time(meeting_start_time), "to", to_time(meeting_end_time))
    else:
        print("No meeting scheduled.")
else:
    print("No feasible schedule found.")