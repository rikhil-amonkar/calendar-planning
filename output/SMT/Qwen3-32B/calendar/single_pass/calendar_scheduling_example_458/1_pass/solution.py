from z3 import *

# Define the solver
solver = Solver()

# Define the start time in minutes since midnight
start_time = Int('start_time')

# Add constraints for the meeting duration and work hours
solver.add(start_time >= 540)  # 9:00 AM
solver.add(start_time + 30 <= 1020)  # 5:00 PM
# Wayne's preference to avoid meetings before 14:00
solver.add(start_time >= 840)  # 14:00 PM

# Define busy intervals for each participant
melissa = [(600, 660), (750, 840), (900, 930)]
gregory = [(750, 780), (930, 960)]
victoria = [(540, 570), (630, 690), (780, 840), (870, 900), (930, 990)]
thomas = [(600, 720), (750, 780), (870, 960)]
jennifer = [(540, 570), (600, 630), (660, 780), (810, 870), (900, 930), (960, 990)]

# Add constraints for all busy intervals
for b_start, b_end in melissa + gregory + victoria + thomas + jennifer:
    solver.add(Or(start_time + 30 <= b_start, start_time >= b_end))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    end_minutes = start_minutes + 30

    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start_minutes)}")
    print(f"End Time: {to_time_str(end_minutes)}")
else:
    print("No solution found.")