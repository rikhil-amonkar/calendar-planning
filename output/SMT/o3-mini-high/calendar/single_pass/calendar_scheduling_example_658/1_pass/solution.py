from z3 import *

# Create the solver
s = Solver()

# Define day: 0 for Monday, 1 for Tuesday
day = Int('day')
s.add(Or(day == 0, day == 1))

# Define meeting start time as minutes offset from 9:00.
# Meeting duration is 30 minutes so meeting_end = meeting_start + 30.
meeting_start = Int('meeting_start')
meeting_end = meeting_start + 30

# The meeting must be within work hours (9:00 to 17:00).
# Since 17:00 is 480 minutes after 9:00, we require meeting_start >= 0 and meeting_end <= 480.
s.add(meeting_start >= 0, meeting_end <= 480)

# ---------------------------
# Monday busy schedules
# ---------------------------
# Shirley on Monday has busy periods:
#   10:30-11:00   -> (90, 120) minutes after 9:00
#   12:00-12:30   -> (180, 210)
#   16:00-16:30   -> (420, 450)
monday_shirley = [(90, 120), (180, 210), (420, 450)]
for (bs, be) in monday_shirley:
    # If meeting is on Monday then it must not overlap the busy interval.
    s.add(Implies(day == 0, Or(meeting_end <= bs, meeting_start >= be)))

# Albert on Monday is busy the entire day: 9:00-17:00 -> (0, 480).
# With a 30-minute meeting, there is no valid slot.
s.add(Implies(day == 0, Or(meeting_end <= 0, meeting_start >= 480)))

# ---------------------------
# Tuesday busy schedules
# ---------------------------
# Shirley on Tuesday is busy:
#   9:30-10:00   -> (30, 60)
tuesday_shirley = [(30, 60)]
for (bs, be) in tuesday_shirley:
    s.add(Implies(day == 1, Or(meeting_end <= bs, meeting_start >= be)))

# Albert on Tuesday is busy:
#   9:30-11:00   -> (30, 120)
#   11:30-12:30  -> (150, 210)
#   13:00-16:00  -> (240, 420)
#   16:30-17:00  -> (450, 480)
tuesday_albert = [(30, 120), (150, 210), (240, 420), (450, 480)]
for (bs, be) in tuesday_albert:
    s.add(Implies(day == 1, Or(meeting_end <= bs, meeting_start >= be)))

# Additionally, Shirley prefers not to meet on Tuesday after 10:30.
# With a 30-minute meeting, that means on Tuesday the meeting must end by 10:30.
# 10:30 is 90 minutes after 9:00, so meeting_end <= 90.
s.add(Implies(day == 1, meeting_end <= 90))

# ---------------------------
# Solve the constraints
# ---------------------------
if s.check() == sat:
    m = s.model()
    # Interpret the day: 0 -> Monday, 1 -> Tuesday.
    scheduled_day = "Monday" if m[day].as_long() == 0 else "Tuesday"
    
    # Compute the start time from minutes after 9:00.
    start_minutes = m[meeting_start].as_long()
    start_hour = 9 + start_minutes // 60
    start_minute = start_minutes % 60
    start_time_str = f"{start_hour:02d}:{start_minute:02d}"
    
    # Compute the end time.
    total_end = start_minutes + 30
    end_hour = 9 + total_end // 60
    end_minute = total_end % 60
    end_time_str = f"{end_hour:02d}:{end_minute:02d}"
    
    # Print the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {scheduled_day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")