from z3 import *

# Define the start time variable in minutes since midnight
S = Int('S')

# Create a solver instance
solver = Solver()

# Add the constraint that the meeting is within 9:00 (540) to 17:00 (1020), duration 30 min
solver.add(And(S >= 540, S <= 990))  # S + 30 <= 1020 => S <= 990

# Function to add constraints for busy intervals
def add_busy_constraints(person_intervals):
    for start, end in person_intervals:
        solver.add(Or(S + 30 <= start, S >= end))

# Define busy intervals for each person in minutes
patrick = [(810, 840), (870, 900)]
shirley = [(540, 570), (660, 690), (720, 750), (870, 900), (960, 1020)]
jeffrey = [(540, 570), (630, 660), (690, 720), (780, 810), (960, 1020)]
gloria = [(690, 720), (900, 930)]
nathan = [(540, 570), (630, 720), (840, 1020)]
angela = [(540, 570), (600, 660), (750, 900), (930, 990)]
david = [(540, 570), (600, 630), (660, 840), (870, 990)]

# Add constraints for each person
add_busy_constraints(patrick)
add_busy_constraints(shirley)
add_busy_constraints(jeffrey)
add_busy_constraints(gloria)
add_busy_constraints(nathan)
add_busy_constraints(angela)
add_busy_constraints(david)

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    start = model[S].as_long()
    
    # Convert minutes to HH:MM format
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = to_time(start)
    end_time = to_time(start + 30)
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found.")