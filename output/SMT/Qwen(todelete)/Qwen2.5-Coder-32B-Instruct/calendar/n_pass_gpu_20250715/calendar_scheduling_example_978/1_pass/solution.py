from z3 import *

# Define variables
day = Int('day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
start_time = Int('start_time')  # in minutes from 00:00

# Define constants for the meeting duration and work hours
meeting_duration = 60  # 1 hour
work_start = 9 * 60  # 09:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Create a solver instance
solver = Solver()

# Add constraints for valid day and start time
solver.add(day >= 0)
solver.add(day <= 4)
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Define busy times for Brian and Julia
brian_busy_times = [
    (0, 9*60 + 30, 10*60),  # Monday 09:30 - 10:00
    (0, 12*60 + 30, 14*60 + 30),  # Monday 12:30 - 14:30
    (0, 15*60 + 30, 16*60),  # Monday 15:30 - 16:00
    (1, 9*60, 9*60 + 30),  # Tuesday 09:00 - 09:30
    (2, 12*60 + 30, 14*60),  # Wednesday 12:30 - 14:00
    (2, 16*60 + 30, 17*60),  # Wednesday 16:30 - 17:00
    (3, 11*60, 11*60 + 30),  # Thursday 11:00 - 11:30
    (3, 13*60, 13*60 + 30),  # Thursday 13:00 - 13:30
    (3, 16*60 + 30, 17*60),  # Thursday 16:30 - 17:00
    (4, 9*60 + 30, 10*60),  # Friday 09:30 - 10:00
    (4, 10*60 + 30, 11*60),  # Friday 10:30 - 11:00
    (4, 13*60, 13*60 + 30),  # Friday 13:00 - 13:30
    (4, 15*60, 16*60),  # Friday 15:00 - 16:00
    (4, 16*60 + 30, 17*60)  # Friday 16:30 - 17:00
]

julia_busy_times = [
    (0, 9*60, 10*60),  # Monday 09:00 - 10:00
    (0, 11*60, 11*60 + 30),  # Monday 11:00 - 11:30
    (0, 12*60 + 30, 13*60),  # Monday 12:30 - 13:00
    (0, 15*60 + 30, 16*60),  # Monday 15:30 - 16:00
    (1, 13*60, 14*60),  # Tuesday 13:00 - 14:00
    (1, 16*60, 16*60 + 30),  # Tuesday 16:00 - 16:30
    (2, 9*60, 11*60 + 30),  # Wednesday 09:00 - 11:30
    (2, 12*60, 12*60 + 30),  # Wednesday 12:00 - 12:30
    (2, 13*60, 17*60),  # Wednesday 13:00 - 17:00
    (3, 9*60, 10*60 + 30),  # Thursday 09:00 - 10:30
    (3, 11*60, 17*60),  # Thursday 11:00 - 17:00
    (4, 9*60, 10*60),  # Friday 09:00 - 10:00
    (4, 10*60 + 30, 11*60 + 30),  # Friday 10:30 - 11:30
    (4, 12*60 + 30, 14*60),  # Friday 12:30 - 14:00
    (4, 14*60 + 30, 15*60),  # Friday 14:30 - 15:00
    (4, 15*60 + 30, 16*60)  # Friday 15:30 - 16:00
]

# Add constraints to avoid busy times
for d, s, e in brian_busy_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + meeting_duration <= s)))

for d, s, e in julia_busy_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + meeting_duration <= s)))

# Prefer avoiding Monday if possible
solver.add(Soft(If(day == 0, 1, 0)))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][model[day].as_long()]
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")