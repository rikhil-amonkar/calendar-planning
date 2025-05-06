from z3 import Solver, Int, Bool, If, And, Optimize, sat

# Travel time from Russian Hill to Pacific Heights.
travel_time = 7

# Starting location: Russian Hill at 9:00AM (540 minutes).
start_time = 540

# Barbara's meeting details:
# Available: from 7:15AM (435) to 10:00PM (1320)
# Minimum meeting duration: 60 minutes.
barbara_avail_start = 435
barbara_avail_end = 1320
barbara_min_time = 60

# Create the Z3 solver.
opt = Optimize()

# Decision variable indicating if we schedule a meeting with Barbara.
x = Bool("barbara_meeting")

# Arrival time at Barbara's location (Pacific Heights).
A = Int("A_barbara")

# If we decide to meet Barbara, then we must travel from Russian Hill.
# Therefore, arrival time A must be at least start time plus travel time.
opt.add(If(x, A >= start_time + travel_time, True))

# Also, if we decide to meet Barbara, then the meeting must be scheduled within her available window.
# The meeting starts at max(A, barbara_avail_start).
meeting_start = If(A < barbara_avail_start, barbara_avail_start, A)
opt.add(If(x, meeting_start + barbara_min_time <= barbara_avail_end, True))

# Also, if meeting, arrival time must be non-negative.
opt.add(A >= 0)

# Objective: maximize the number of friends met.
# Since there is only one friend, we maximize x being True.
opt.maximize(If(x, 1, 0))

if opt.check() == sat:
    model = opt.model()
    scheduled = model.evaluate(x)
    if scheduled:
        arrival = model.evaluate(A).as_long()
        # Meeting actually starts at the later of the arrival time and Barbara's available start.
        start_meeting = arrival if arrival >= barbara_avail_start else barbara_avail_start
        end_meeting = start_meeting + barbara_min_time
        
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        print("Meeting scheduled with Barbara at Pacific Heights:")
        print(f" - Arrival time: {to_time(arrival)}")
        print(f" - Meeting from: {to_time(start_meeting)} to {to_time(end_meeting)}")
    else:
        print("No meeting with Barbara is scheduled.")
else:
    print("No feasible schedule found.")