from z3 import *

# Define day variable: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day = Int('day')
# Define meeting start time as minutes after 9:00.
start = Int('start')
duration = 60
end = start + duration

s = Solver()

# Working window: meeting must start between 9:00 and 16:00 (i.e. 0 and 420 minutes after 9:00)
s.add(day >= 0, day <= 4)
s.add(start >= 0, start <= 420)

# Preferences:
# Bryan would like to avoid Tuesday (day 1)
s.add(day != 1)
# Nicholas would rather not meet on Monday (day 0) or Thursday (day 3)
s.add(day != 0, day != 3)

# Busy schedules are given by (day, busy_start, busy_end) in minutes from 9:00.
# Bryan's busy intervals:
bryan_busy = [
    (3, 30, 60),    # Thursday: 9:30-10:00 (9:00+30 to 9:00+60)
    (3, 210, 240),  # Thursday: 12:30-13:00
    (4, 90, 120),   # Friday: 10:30-11:00
    (4, 300, 330)   # Friday: 14:00-14:30
]

# Nicholas's busy intervals:
nicholas_busy = [
    (0, 150, 180),  # Monday: 11:30-12:00 (11:30-9:00=150, 12:00-9:00=180)
    (0, 240, 390),  # Monday: 13:00-15:30
    (1, 0, 30),     # Tuesday: 9:00-9:30
    (1, 120, 270),  # Tuesday: 11:00-13:30
    (1, 300, 450),  # Tuesday: 14:00-16:30
    (2, 0, 30),     # Wednesday: 9:00-9:30
    (2, 60, 120),   # Wednesday: 10:00-11:00
    (2, 150, 270),  # Wednesday: 11:30-13:30
    (2, 300, 330),  # Wednesday: 14:00-14:30
    (2, 360, 450),  # Wednesday: 15:00-16:30
    (3, 90, 150),   # Thursday: 10:30-11:30
    (3, 180, 210),  # Thursday: 12:00-12:30
    (3, 360, 390),  # Thursday: 15:00-15:30
    (3, 450, 480),  # Thursday: 16:30-17:00
    (4, 0, 90),     # Friday: 9:00-10:30
    (4, 120, 180),  # Friday: 11:00-12:00
    (4, 210, 330),  # Friday: 12:30-14:30
    (4, 390, 420),  # Friday: 15:30-16:00
    (4, 450, 480)   # Friday: 16:30-17:00
]

# For each busy interval for Bryan, if the meeting is scheduled on that day then it must not overlap the busy slot.
for d, b_start, b_end in bryan_busy:
    s.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# Similarly, enforce non-overlap with Nicholas's busy intervals.
for d, b_start, b_end in nicholas_busy:
    s.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    sol_day = m[day].as_long()
    sol_start = m[start].as_long()
    
    # Convert meeting start minutes (after 9:00) into HH:MM format.
    meeting_hour = 9 + sol_start // 60
    meeting_minute = sol_start % 60
    meeting_start_str = f"{meeting_hour:02d}:{meeting_minute:02d}"
    
    # Meeting end time.
    sol_end = sol_start + duration
    meeting_hour_end = 9 + sol_end // 60
    meeting_minute_end = sol_end % 60
    meeting_end_str = f"{meeting_hour_end:02d}:{meeting_minute_end:02d}"
    
    # Map day number back to day names.
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    sol_day_str = day_names[sol_day]
    
    print("SOLUTION:")
    print(f"Day: {sol_day_str}")
    print(f"Start Time: {meeting_start_str}")
    print(f"End Time: {meeting_end_str}")
else:
    print("No solution found")