from z3 import *

# Define the start time variable in minutes since midnight
S = Int('S')

solver = Solver()

# Add constraints for the time window (9:00 to 12:00 PM for start)
solver.add(S >= 540)  # 9:00 AM
solver.add(S <= 720)  # 12:00 PM (meeting must end by 12:30 PM)

# Function to add busy intervals constraints
def add_busy_constraints(participant_busies):
    for start, end in participant_busies:
        # The meeting [S, S+30) does not overlap with [start, end)
        # So S + 30 <= start OR S >= end
        solver.add(Or(S + 30 <= start, S >= end))

# Add Jack's busy constraints
jack_busies = [(570, 630), (660, 690), (750, 780), (840, 870), (960, 990)]
add_busy_constraints(jack_busies)

# Add Charlotte's busy constraints
charlotte_busies = [(570, 600), (630, 720), (750, 810), (840, 960)]
add_busy_constraints(charlotte_busies)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_min = model[S].as_long()
    # Convert start_min to hours and minutes
    start_h = start_min // 60
    start_m = start_min % 60
    end_min = start_min + 30
    end_h = end_min // 60
    end_m = end_min % 60
    # Format as strings with leading zeros
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")