from z3 import Solver, Int, Or

# We represent time in minutes relative to 9:00.
# Thus 9:00 is 0 minutes, 14:00 is 300 minutes and 17:00 is 480 minutes.
# The meeting duration is 30 minutes.

s = Solver()
meeting_start = Int("meeting_start")
duration = 30
meeting_end = meeting_start + duration

# Constraint: Meeting must be within work hours (9:00-17:00)
s.add(meeting_start >= 0)
s.add(meeting_end <= 480)

# Wayne prefers not to have meetings before 14:00
s.add(meeting_start >= 300)  # 14:00 is 300 minutes after 9:00

# List busy intervals (in minutes from 9:00) for each participant

# Melissa's busy intervals:
#   10:00-11:00 -> (60, 120)
#   12:30-14:00 -> (210, 300)
#   15:00-15:30 -> (360, 390)
melissa_busy = [(60, 120), (210, 300), (360, 390)]

# Gregory's busy intervals:
#   12:30-13:00 -> (210, 240)
#   15:30-16:00 -> (390, 420)
gregory_busy = [(210, 240), (390, 420)]

# Victoria's busy intervals:
#   9:00-9:30   -> (0, 30)
#   10:30-11:30 -> (90, 150)
#   13:00-14:00 -> (240, 300)
#   14:30-15:00 -> (330, 360)
#   15:30-16:30 -> (390, 450)
victoria_busy = [(0, 30), (90, 150), (240, 300), (330, 360), (390, 450)]

# Thomas's busy intervals:
#   10:00-12:00 -> (60, 180)
#   12:30-13:00 -> (210, 240)
#   14:30-16:00 -> (330, 420)
thomas_busy = [(60, 180), (210, 240), (330, 420)]

# Jennifer's busy intervals:
#   9:00-9:30    -> (0, 30)
#   10:00-10:30  -> (60, 90)
#   11:00-13:00  -> (120, 240)
#   13:30-14:30  -> (270, 330)
#   15:00-15:30  -> (360, 390)
#   16:00-16:30  -> (420, 450)
jennifer_busy = [(0, 30), (60, 90), (120, 240), (270, 330), (360, 390), (420, 450)]

# Wayne and Catherine are free all day (subject only to Wayne's preference).
# Combine all busy intervals into one list.
busy_intervals = melissa_busy + gregory_busy + victoria_busy + thomas_busy + jennifer_busy

# For each busy interval, ensure that the meeting does not overlap the busy time.
# Assuming that if the meeting ends exactly when a busy interval starts (or vice versa) it is acceptable.
for (bs, be) in busy_intervals:
    s.add(Or(meeting_end <= bs, meeting_start >= be))

# Solve the constraints.
if s.check() == 'sat':
    model = s.model()
    start = model[meeting_start].as_long()
    end = start + duration

    # Convert from minutes offset (from 9:00) to HH:MM in 24-hour format.
    # 9:00 corresponds to 9*60 = 540 minutes from midnight.
    def minutes_to_time(minutes_offset):
        total_minutes = 540 + minutes_offset
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    start_time_str = minutes_to_time(start)
    end_time_str = minutes_to_time(end)
    
    output = f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
    print(output)
else:
    print("No solution found")