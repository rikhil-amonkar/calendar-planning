from z3 import Optimize, Int, Bool, If, And, Or, sat

# Locations:
# Russian Hill (starting point) and Richmond District.
# Travel times (in minutes):
# Russian Hill -> Richmond District: 14
# Richmond District -> Russian Hill: 13 (not used in this one-way journey)
travel = {
    ("Russian Hill", "Richmond District"): 14,
    ("Richmond District", "Russian Hill"): 13
}

# Friend meeting information:
# Barbara is at Richmond District.
# Availability: from 1:15PM (795 minutes) to 6:15PM (1095 minutes)
# Minimum meeting duration: 45 minutes.
friend_loc = "Richmond District"
avail_start = 795
avail_end = 1095
min_duration = 45

# You arrive at Russian Hill (starting point) at 9:00AM = 540 minutes.
start_loc = "Russian Hill"
start_time = 540

# Create the Z3 optimizer.
opt = Optimize()

# Decision variables:
# x: Boolean indicating whether you meet Barbara.
# A: Arrival time (in minutes) at Barbara's location (Richmond District).
# order: Since there is only one friend, if scheduled,
#        the order is 0; if not scheduled, we set it to -1.
x = Bool("x")
A = Int("A")         # Arrival time at Richmond District.
order = Int("order") # Meeting order.

# If meeting is scheduled, order must be 0, else set to -1.
opt.add(If(x, order == 0, order == -1))
opt.add(A >= 0)

# Constraint: Travel from Russian Hill to Richmond District takes 14 minutes.
# If you decide to meet Barbara (x is True and order is 0), your arrival time must be at least start_time + travel.
if ("Russian Hill", "Richmond District") in travel:
    travel_time = travel[("Russian Hill", "Richmond District")]
else:
    travel_time = 0
opt.add(Or(Not(x), order != 0, A >= start_time + travel_time))

# Meeting availability constraint:
# The meeting starts at the later of your arrival time and Barbara's avail_start.
# It must last at least min_duration minutes and finish by avail_end.
meeting_start = If(A < avail_start, avail_start, A)
opt.add(Or(Not(x), meeting_start + min_duration <= avail_end))

# Objective: maximize the number of friends met (Barbara in this case).
opt.maximize(If(x, 1, 0))

# Solve and display the result.
if opt.check() == sat:
    model = opt.model()
    meet = model.eval(x)
    print("Optimal meeting schedule:")
    def to_time(t):
        # Format minutes to HH:MM (24-hour format)
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"
    
    if meet:
        arrival = model.eval(A).as_long()
        actual_start = arrival if arrival >= avail_start else avail_start
        meeting_end = actual_start + min_duration
        print("Meet Barbara at Richmond District:")
        print("  Arrival time:", to_time(arrival))
        print("  Meeting from", to_time(actual_start), "to", to_time(meeting_end))
    else:
        print("No meeting scheduled with Barbara.")
else:
    print("No feasible meeting schedule found.")