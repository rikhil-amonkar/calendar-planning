from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solver = Solver()
start = Int('start')
# Meeting must be between 9:00 (540) and 17:00 (1020), 30 minutes duration
solver.add(And(start >= 540, start + 30 <= 1020))
# Roger prefers not before 12:30 (750)
solver.add(start >= 750)

# Define busy intervals for each participant (converted to minutes since midnight)
busy_intervals = {
    'Kathleen': [(14*60 + 30, 15*60 + 30)],  # 14:30-15:30
    'Carolyn': [(12*60, 12*60 + 30), (13*60, 13*60 + 30)],  # 12:00-12:30, 13:00-13:30
    'Cheryl': [(9*60, 9*60 + 30), (10*60, 11*60 + 30), (12*60 + 30, 13*60 + 30), (14*60, 17*60)],  # 9:00-9:30, 10:00-11:30, 12:30-13:30, 14:00-17:00
    'Virginia': [(9*60 + 30, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60 + 30), (16*60, 17*60)],  # 9:30-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:30, 16:00-17:00
    'Angela': [(9*60 + 30, 10*60), (10*60 + 30, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (14*60, 16*60 + 30)]  # 9:30-10:00, 10:30-11:30, 12:00-12:30, 13:00-13:30, 14:00-16:30
}

# Add constraints for all busy intervals
for intervals in busy_intervals.values():
    for (b_start, b_end) in intervals:
        solver.add(Or(start + 30 <= b_start, start >= b_end))

if solver.check() == sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    day = "Monday"
    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(end_val)
    print(f"{{ {start_time}:{end_time} }} {day}")
else:
    print("No solution found")