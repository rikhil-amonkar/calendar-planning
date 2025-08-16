from z3 import *

# Define the busy intervals for Laura and Philip on each day
laura_busy = {
    0: [(90, 120), (210, 240), (330, 390), (420, 480)],
    1: [(30, 60), (120, 150), (240, 270), (330, 360), (420, 480)],
    3: [(90, 120), (180, 270), (360, 390), (420, 450)]
}

philip_busy = {
    0: [(0, 480)],
    1: [(0, 120), (150, 180), (240, 270), (300, 330), (360, 450)],
    3: [(0, 90), (120, 210), (240, 480)]
}

# Initialize Z3 solver
solver = Solver()

# Define variables
day = Int('day')
start = Int('start')

# Add constraints for day and start time
solver.add(Or(day == 0, day == 1, day == 3))  # Exclude Wednesday
solver.add(And(start >= 0, start <= 420))     # Ensure meeting fits within 9-17

# Add constraints for each busy interval
for d in [0, 1, 3]:
    for b_start, b_end in laura_busy.get(d, []):
        cond = Implies(day == d, Or(start + 60 <= b_start, start >= b_end))
        solver.add(cond)
    for b_start, b_end in philip_busy.get(d, []):
        cond = Implies(day == d, Or(start + 60 <= b_start, start >= b_end))
        solver.add(cond)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    
    # Convert day to name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = days[day_val]
    
    # Convert start and end times to HH:MM format
    def to_time(minutes_since_9am):
        hours = 9 + (minutes_since_9am // 60)
        mins = minutes_since_9am % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time_str = to_time(start_val)
    end_time_str = to_time(start_val + 60)
    
    # Output the solution
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")