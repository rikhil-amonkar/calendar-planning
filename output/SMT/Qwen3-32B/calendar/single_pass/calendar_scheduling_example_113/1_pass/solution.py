import z3

# Initialize solver
solver = z3.Solver()

# Define start time variable in minutes since midnight
start = z3.Int('start')

# Add constraints for work hours (9:00-17:00, 540-1020 minutes)
# Meeting must start at least 30 minutes before 17:00, so latest start is 990
solver.add(start >= 540)
solver.add(start <= 990)

# Bradley's busy intervals (in minutes)
bradley = [(570, 600), (750, 780), (810, 840), (930, 960)]
for b_start, b_end in bradley:
    solver.add(z3.Or(start + 30 <= b_start, b_end <= start))

# Teresa's busy intervals
teresa = [(630, 660), (720, 750), (780, 810), (870, 900)]
for b_start, b_end in teresa:
    solver.add(z3.Or(start + 30 <= b_start, b_end <= start))

# Elizabeth's busy intervals
elizabeth = [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)]
for b_start, b_end in elizabeth:
    solver.add(z3.Or(start + 30 <= b_start, b_end <= start))

# Christian's busy intervals
christian = [(540, 570), (630, 1020)]
for b_start, b_end in christian:
    solver.add(z3.Or(start + 30 <= b_start, b_end <= start))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    
    # Convert minutes to HH:MM format
    def to_time(m):
        hours = m // 60
        mins = m % 60
        return f"{hours:02d}:{mins:02d}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found.")