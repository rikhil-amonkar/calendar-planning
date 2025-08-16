import z3

# Initialize solver
solver = z3.Solver()

# Define start time variable (in minutes since midnight)
start = z3.Int('start')

# Work hours are from 9:00 (540) to 17:00 (1020). The meeting is 30 minutes long, so start must be <= 990 (16:30)
solver.add(start >= 540)
solver.add(start <= 990)

# Define all participants' busy intervals (converted to minutes since midnight)
emily = [(600, 630), (960, 990)]  # 10:00-10:30, 16:00-16:30
maria = [(630, 660), (840, 870)]  # 10:30-11:00, 14:00-14:30
carl = [(570, 600), (630, 750), (810, 840), (870, 930), (960, 1020)]  # 9:30-10:00, 10:30-12:30, 13:30-14:00, 14:30-15:30, 16:00-17:00
david = [(570, 660), (690, 720), (750, 780), (840, 900), (960, 1020)]  # 9:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-15:00, 16:00-17:00
frank = [(570, 630), (660, 690), (750, 780), (870, 1020)]  # 9:30-10:30, 11:00-11:30, 12:30-13:30, 14:30-17:00

# Combine all intervals
all_intervals = emily + maria + carl + david + frank

# Add constraints for each interval
for s, e in all_intervals:
    solver.add(z3.Or(start >= e, start + 30 <= s))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    
    # Convert minutes to HH:MM format
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(start_val + 30)}")
else:
    print("No solution found.")