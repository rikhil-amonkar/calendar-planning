import z3

# Initialize the solver
solver = z3.Optimize()

# Define the start time variable in minutes since midnight
start = z3.Int('start')

# Work hours from 9:00 (540) to 17:00 (1020), meeting duration is 30 minutes
# Start must be between 540 and 990 (inclusive)
solver.add(z3.And(start >= 540, start <= 990))

# Lisa's busy intervals (in minutes since midnight)
lisa_busy = [(540, 570), (630, 660), (840, 960)]

# Anthony's busy intervals (in minutes since midnight)
anthony_busy = [(540, 570), (660, 690), (750, 810), (840, 900), (930, 960), (990, 1020)]

# Add constraints for each busy interval to avoid overlap
for s, e in lisa_busy + anthony_busy:
    solver.add(z3.Or(start >= e, start + 30 <= s))

# Minimize the start time to find the earliest possible meeting time
solver.minimize(start)

# Check if a solution exists
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    
    # Convert start time to HH:MM format
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    
    # Format with leading zeros
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found")