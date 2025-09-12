from z3 import *

# Create solver instance
solver = Solver()

# Variables
day = Int('day')
start = Int('start')

# Constraints for day and start time
solver.add(Or(day == 1, day == 3))  # Tuesday (1) or Thursday (3)
solver.add(start >= 540, start <= 960)  # 9:00 to 16:00

# Helper function to add non-overlapping constraints for intervals
def add_non_overlap_constraints(participant_intervals, day_value):
    for s, e in participant_intervals:
        solver.add(Implies(day == day_value, Or(start + 60 <= s, e <= start)))

# Tuesday (day == 1) intervals
# Laura's busy times on Tuesday
laura_tue_intervals = [
    (570, 600),  # 9:30-10:00
    (660, 690),  # 11:00-11:30
    (780, 810),  # 13:00-13:30
    (870, 900),  # 14:30-15:00
    (960, 1020)  # 16:00-17:00
]
# Philip's busy times on Tuesday
philip_tue_intervals = [
    (540, 660),  # 9:00-11:00
    (690, 720),  # 11:30-12:00
    (780, 810),  # 13:00-13:30
    (840, 870),  # 14:00-14:30
    (900, 990)   # 15:00-16:30
]
add_non_overlap_constraints(laura_tue_intervals, 1)
add_non_overlap_constraints(philip_tue_intervals, 1)

# Thursday (day == 3) intervals
# Laura's busy times on Thursday
laura_thu_intervals = [
    (630, 660),  # 10:30-11:00
    (720, 810),  # 12:00-13:30
    (900, 930),  # 15:00-15:30
    (960, 990)   # 16:00-16:30
]
# Philip's busy times on Thursday
philip_thu_intervals = [
    (540, 630),  # 9:00-10:30
    (660, 750),  # 11:00-12:30
    (780, 1020)  # 13:00-17:00
]
add_non_overlap_constraints(laura_thu_intervals, 3)
add_non_overlap_constraints(philip_thu_intervals, 3)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    day_val = model.eval(day).as_long()
    start_val = model.eval(start).as_long()
    end_val = start_val + 60

    # Convert day to name
    day_name = ''
    if day_val == 1:
        day_name = 'Tuesday'
    elif day_val == 3:
        day_name = 'Thursday'

    # Convert start and end times to HH:MM format
    def to_time_str(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_str = to_time_str(start_val)
    end_str = to_time_str(end_val)
    print(f"{start_str}:{end_str} {day_name}")
else:
    print("No solution found")