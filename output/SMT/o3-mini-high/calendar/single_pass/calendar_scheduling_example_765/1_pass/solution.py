from z3 import *

# We'll represent days as integers:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday
# Time is represented in minutes from 9:00.
# Since work hours are 9:00 to 17:00, start ∈ [0, 450] (because meeting duration is 30 minutes).

# Create Z3 solver and variables.
solver = Solver()
day = Int('day')       # Meeting day: 0=Monday, 1=Tuesday, 2=Wednesday.
start = Int('start')   # Meeting start time in minutes after 9:00.

# Basic domain constraints.
solver.add(Or(day == 0, day == 1, day == 2))
solver.add(start >= 0, start + 30 <= 480)  # Meeting must finish by 17:00.

# Tuesday is impossible for Joyce (busy 9:00-17:00), so force meeting day ≠ Tuesday.
solver.add(day != 1)

# Helper function: if the meeting is on a specific day, then the meeting must avoid the busy interval.
def no_overlap(day_val, busy_start, busy_end):
    # Meeting [start, start+30) must not overlap busy interval [busy_start, busy_end).
    return If(day == day_val, Or(start + 30 <= busy_start, start >= busy_end), True)

# Add constraints for Joshua's busy schedule.
# Joshua is busy on:
# Monday: 15:00 to 15:30 --> [360, 390)
solver.add(no_overlap(0, 360, 390))
# Tuesday: 11:30-12:00, 13:00-13:30, 14:30-15:00 (Tuesday is not available anyway).
solver.add(If(day == 1, Or(start + 30 <= 150, start >= 180), True))  # [11:30,12:00] (150,180)
solver.add(If(day == 1, Or(start + 30 <= 240, start >= 270), True))  # [13:00,13:30] (240,270)
solver.add(If(day == 1, Or(start + 30 <= 330, start >= 360), True))  # [14:30,15:00] (330,360)
# Joshua has no meetings on Wednesday.

# Add constraints for Joyce's busy schedule.
# Joyce is busy on:
# Monday:
#   9:00 to 9:30 --> [0, 30)
solver.add(no_overlap(0, 0, 30))
#   10:00 to 11:00 --> [60, 120)
solver.add(no_overlap(0, 60, 120))
#   11:30 to 12:30 --> [150, 210)
solver.add(no_overlap(0, 150, 210))
#   13:00 to 15:00 --> [240, 360)
solver.add(no_overlap(0, 240, 360))
#   15:30 to 17:00 --> [390, 480)
solver.add(no_overlap(0, 390, 480))
# Plus, Joyce prefers not to have meetings on Monday before 12:00.
# (12:00 corresponds to 180 minutes after 9:00.)
solver.add(If(day == 0, start >= 180, True))

# Tuesday:
#   Joyce is busy the entire day (9:00 to 17:00).
# (Since day != 1 is enforced, we can skip explicit Tuesday constraints.)

# Wednesday:
#   Busy from 9:00 to 9:30 --> [0, 30)
solver.add(no_overlap(2, 0, 30))
#   Busy from 10:00 to 11:00 --> [60, 120)
solver.add(no_overlap(2, 60, 120))
#   Busy from 12:30 to 15:30 --> [210, 390)
solver.add(no_overlap(2, 210, 390))
#   Busy from 16:00 to 16:30 --> [420, 450)
solver.add(no_overlap(2, 420, 450))

# Now, check for a solution.
if solver.check() == sat:
    m = solver.model()
    meeting_day = m[day].as_long()
    meeting_start = m[start].as_long()
    # Convert meeting_start (minutes from 9:00) to HH:MM format.
    actual_hour = 9 + meeting_start // 60
    actual_min = meeting_start % 60
    meeting_end = meeting_start + 30
    end_hour = 9 + meeting_end // 60
    end_min = meeting_end % 60

    # Map the day integer to a string.
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[meeting_day]

    # Output in the required format.
    print("SOLUTION:")
    print("Day: " + day_str)
    print("Start Time: {:02d}:{:02d}".format(actual_hour, actual_min))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_min))
else:
    print("No solution found.")