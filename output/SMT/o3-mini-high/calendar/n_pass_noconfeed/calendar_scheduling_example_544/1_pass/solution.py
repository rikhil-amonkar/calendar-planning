from z3 import Solver, Int, sat

def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting duration in minutes
duration = 30

# Define time boundaries in minutes from midnight.
work_start = 9 * 60   # 9:00 AM = 540 minutes
work_end   = 17 * 60  # 17:00 = 1020 minutes
latest_meeting_end_for_albert = 11 * 60  # 11:00 AM = 660 minutes

# Albert's blocked intervals (represented in minutes).
# Block 1: 9:00 - 10:00 --> [540, 600)
# Block 2: 10:30 - 12:00 --> [630, 720)
# Block 3: 15:00 - 16:30 --> [900, 990) 
# (Block 3 is out of our overall consideration because of the after 11:00 constraint)

# We represent the meeting start time as an integer (minutes from midnight)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + duration

s = Solver()

# 1. The meeting must be within work hours.
s.add(meeting_start >= work_start)
s.add(meeting_end <= work_end)

# 2. Albert cannot meet after 11:00, so the meeting must end by 11:00.
s.add(meeting_end <= latest_meeting_end_for_albert)

# 3. Respect Albert's blocked times.
# For two time intervals [a, b) and [c, d) not to overlap, we require either:
#   meeting_end <= block_start OR meeting_start >= block_end.

# For Block 1: [540, 600)
# Since meeting_start cannot be before 540 and the meeting duration is positive,
# we must have the meeting start at or after the end of this block.
s.add(meeting_start >= 600)

# For Block 2: [630, 720)
# Given our time limits, the only possibility is that the meeting ends by 10:30.
# In other words, meeting_end must be <= 630.
s.add(meeting_end <= 630)

# Block 3 is irrelevant because meeting_end is already constrained to be <= 660.

if s.check() == sat:
    m = s.model()
    start_val = m[meeting_start].as_long()
    end_val = start_val + duration
    # Format meeting time in HH:MM:HH:MM format along with the day.
    meeting_time_str = f"{minutes_to_str(start_val)}:{minutes_to_str(end_val)}"
    print(f"{meeting_time_str} Monday")
else:
    print("No solution found.")