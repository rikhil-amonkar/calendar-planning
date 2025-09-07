from z3 import *

def minutes_to_time(offset):
    total_minutes = 9 * 60 + offset
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

solver = Solver()

# Define the day (0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday)
day = Int('day')
solver.add(Or(day == 0, day == 1, day == 2, day == 3))
solver.add(day == 3)  # Force meeting on Thursday

# Define meeting start time as minutes offset from 9:00
start = Int('start')
solver.add(start >= 0, start <= 450)

meeting_duration = 30  # meeting duration of 30 minutes (0.5 hour)

# Ensure the meeting fits into the desired window: 14:30 to 15:00
solver.add(start >= 330)              # 14:30 is 9:00 + 330 minutes
solver.add(start + meeting_duration <= 360)  # 15:00 is 9:00 + 360 minutes

if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + meeting_duration

    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    chosen_day = day_names[day_val]

    start_time = minutes_to_time(start_val)
    end_time = minutes_to_time(end_val)

    print(f"{chosen_day} {start_time}:{end_time}")
else:
    print("No solution found.")