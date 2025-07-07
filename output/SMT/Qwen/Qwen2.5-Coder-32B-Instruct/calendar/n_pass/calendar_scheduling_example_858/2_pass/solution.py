from z3 import *

# Define the variables
day = Int('day')
start_time = Int('start_time')

# Define the domain for the variables
days = {'Monday': 1, 'Tuesday': 2, 'Wednesday': 3, 'Thursday': 4}
day_domain = And(day >= 1, day <= 4)

# Meeting duration is 1 hour
meeting_duration = 60

# Carl's busy times
carl_busy_times = [
    (1, 11*60 + 0, 11*60 + 30),  # Monday 11:00 to 11:30
    (2, 14*60 + 30, 15*60 + 0), # Tuesday 14:30 to 15:00
    (3, 10*60 + 0, 11*60 + 30),  # Wednesday 10:00 to 11:30
    (3, 13*60 + 0, 13*60 + 30),  # Wednesday 13:00 to 13:30
    (4, 13*60 + 30, 14*60 + 0), # Thursday 13:30 to 14:00
    (4, 16*60 + 0, 16*60 + 30)  # Thursday 16:00 to 16:30
]

# Margaret's busy times
margaret_busy_times = [
    (1, 9*60 + 0, 10*60 + 30),  # Monday 9:00 to 10:30
    (1, 11*60 + 0, 17*60 + 0),  # Monday 11:00 to 17:00
    (2, 9*60 + 30, 12*60 + 0), # Tuesday 9:30 to 12:00
    (2, 13*60 + 30, 14*60 + 0),# Tuesday 13:30 to 14:00
    (2, 15*60 + 30, 17*60 + 0),# Tuesday 15:30 to 17:00
    (3, 9*60 + 30, 12*60 + 0), # Wednesday 9:30 to 12:00
    (3, 12*60 + 30, 13*60 + 0),# Wednesday 12:30 to 13:00
    (3, 13*60 + 30, 14*60 + 0),# Wednesday 13:30 to 14:30
    (3, 15*60 + 0, 17*60 + 0),  # Wednesday 15:00 to 17:00
    (4, 10*60 + 0, 12*60 + 0), # Thursday 10:00 to 12:00
    (4, 12*60 + 30, 14*60 + 0),# Thursday 12:30 to 14:00
    (4, 14*60 + 30, 17*60 + 0) # Thursday 14:30 to 17:00
]

# Define constraints
constraints = [day_domain]

# Add constraints for Carl's busy times
for d, s, e in carl_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Margaret's busy times
for d, s, e in margaret_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Ensure the meeting is within work hours (9:00 to 17:00)
work_start = 9 * 60
work_end = 17 * 60
constraints.append(And(start_time >= work_start, start_time + meeting_duration <= work_end))

# Carl prefers not to meet on Thursday
constraints.append(day != 4)

# Solve the problem
s = Solver()
s.add(constraints)

if s.check() == sat:
    model = s.model()
    meeting_day = [k for k, v in days.items() if v == model[day].as_long()][0]
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time//60}:{meeting_start_time%60:02}\nEnd Time: {meeting_end_time//60}:{meeting_end_time%60:02}")
else:
    print("No solution found")