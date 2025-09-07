from z3 import *

# Define busy periods for each participant in minutes since midnight
jack_busy = [(540, 570), (840, 870)]
madison_busy = [(570, 630), (780, 840), (900, 930), (990, 1020)]
rachel_busy = [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)]
douglas_busy = [(540, 690), (720, 990)]
ryan_busy = [(540, 570), (780, 840), (870, 1020)]

# Combine all busy periods
all_busies = jack_busy + madison_busy + rachel_busy + douglas_busy + ryan_busy

# Initialize solver and variable
solver = Solver()
start = Int('start')

# Add constraints for valid meeting time (9:00-17:00, 30 minutes duration)
solver.add(And(start >= 540, start <= 990))  # 9:00-17:00 in minutes (start <= 1020-30)

# Add constraints for non-overlapping with busy periods
for s, e in all_busies:
    solver.add(Or(start >= e, start + 30 <= s))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30

    # Convert start and end times to HH:MM format
    start_h, start_m = divmod(start_val, 60)
    end_h, end_m = divmod(end_val, 60)
    print(f"Monday {start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}")
else:
    print("No solution found")