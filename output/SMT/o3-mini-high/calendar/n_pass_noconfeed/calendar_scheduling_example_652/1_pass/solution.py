from z3 import *

# Meeting parameters
meeting_duration = 30  # in minutes

# Working hours (relative to 9:00 AM, in minutes)
work_start = 0         # 9:00 AM
work_end   = 480       # 17:00 (9:00 AM + 480 minutes)
# Additionally, on Tuesday Lawrence cannot meet after 16:30 (which is 450 minutes after 9:00)
tuesday_end = 450

# Create Z3 solver
s = Solver()

# Define day: 0 represents Monday, 1 represents Tuesday
day = Int('day')
s.add(Or(day == 0, day == 1))

# Define meeting start time in minutes after 9:00 AM
start = Int('start')
s.add(start >= work_start)
# If it's Tuesday, meeting must finish by 16:30, otherwise by 17:00.
s.add(If(day == 1, start + meeting_duration <= tuesday_end, start + meeting_duration <= work_end))

# --------------------
# Participant Schedules
# --------------------

# Jesse's schedule:
# Monday: busy 13:30-14:00 (i.e., 270-300) and 14:30-15:00 (i.e., 330-360)
s.add(Implies(day == 0, Or(start + meeting_duration <= 270, start >= 300)))
s.add(Implies(day == 0, Or(start + meeting_duration <= 330, start >= 360)))

# Tuesday: busy 9:00-9:30 (i.e., 0-30), 13:00-13:30 (240-270), and 14:00-15:00 (300-360)
s.add(Implies(day == 1, start >= 30))  # Cannot start at 9:00 since Jesse is busy from 9:00
s.add(Implies(day == 1, Or(start + meeting_duration <= 240, start >= 270)))
s.add(Implies(day == 1, Or(start + meeting_duration <= 300, start >= 360)))

# Lawrence's schedule:
# Monday: busy the entire day from 9:00 to 17:00 ==> No meeting possible on Monday.
s.add(Implies(day == 0, False))

# Tuesday: busy 9:30-10:30 (30-90), 11:30-12:30 (150-210), 13:00-13:30 (240-270),
#          14:30-15:00 (330-360), and 15:30-16:30 (390-450)
s.add(Implies(day == 1, Or(start + meeting_duration <= 30,  start >= 90)))
s.add(Implies(day == 1, Or(start + meeting_duration <= 150, start >= 210)))
s.add(Implies(day == 1, Or(start + meeting_duration <= 240, start >= 270)))
s.add(Implies(day == 1, Or(start + meeting_duration <= 330, start >= 360)))
s.add(Implies(day == 1, Or(start + meeting_duration <= 390, start >= 450)))

# --------------------
# Solve the constraints
# --------------------
if s.check() == sat:
    m = s.model()
    meeting_day = "Monday" if m[day].as_long() == 0 else "Tuesday"
    start_minutes = m[start].as_long()
    
    # Convert the start time (minutes after 9:00) to an absolute time in HH:MM format.
    start_hour = 9 + start_minutes // 60
    start_min  = start_minutes % 60
    end_total  = start_minutes + meeting_duration
    end_hour   = 9 + end_total // 60
    end_min    = end_total % 60
    
    meeting_time = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print(f"{meeting_day} {meeting_time}")
else:
    print("No meeting time found")