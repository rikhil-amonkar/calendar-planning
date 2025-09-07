from z3 import *

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create solver
solver = Solver()

# Define start time variable (in minutes since midnight)
start_time = Int('start_time')

# Add constraints for valid time window (9:00-17:00) and Pamela's preference (<=14:30)
solver.add(start_time >= 9 * 60)          # 9:00 AM
solver.add(start_time <= 13 * 60 + 30)    # 13:30 PM (meeting must end by 14:30)

# Anthony's busy times (in minutes)
anthony_busies = [(9*60 + 30, 10*60), (12*60, 13*60), (16*60, 16*60 + 30)]
for b_start, b_end in anthony_busies:
    solver.add(Or(start_time + 60 <= b_start, start_time >= b_end))

# Pamela's busy times
pamela_busies = [(9*60 + 30, 10*60), (16*60 + 30, 17*60)]
for b_start, b_end in pamela_busies:
    solver.add(Or(start_time + 60 <= b_start, start_time >= b_end))

# Zachary's busy times
zachary_busies = [(9*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)]
for b_start, b_end in zachary_busies:
    solver.add(Or(start_time + 60 <= b_start, start_time >= b_end))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    end_minutes = start_minutes + 60
    start_str = minutes_to_time(start_minutes)
    end_str = minutes_to_time(end_minutes)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")