from z3 import *

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting parameters
duration = 30  # meeting duration in minutes
work_start = 9 * 60    # 9:00 in minutes since midnight
work_end   = 17 * 60   # 17:00 in minutes since midnight
latest_end_for_helen = 13 * 60 + 30  # 13:30 in minutes since midnight

# We will measure meeting start time, m, as minutes after 9:00.
# Hence, actual meeting start time in minutes since midnight = work_start + m.
# Note: m must be chosen so that work_start+m+duration is within working hours.
# Also Helen requires: work_start + m + duration <= latest_end_for_helen.
# Converting these back to our relative minutes (offset from 9:00):
#   m + duration <= (work_end - work_start)    and
#   m + duration <= (latest_end_for_helen - work_start)
# work_end - work_start = 480 and latest_end_for_helen - work_start = 270.
    
# Create the solver and meeting start variable (in minutes offset from 9:00)
s = Solver()
m = Int('m')
s.add(m >= 0, m + duration <= 480)    # within 9:00 to 17:00
s.add(m + duration <= 270)            # Helen's constraint: meeting must end by 13:30

# Helper: For a meeting starting at m (lasting 'duration' minutes) and a blocked interval [a, b]
# (both a and b given as minutes offset from 9:00), the meeting and the blocked interval must not overlap.
def no_overlap(m, a, b):
    # They do not overlap if meeting ends on or before a, or starts on or after b.
    return Or(m + duration <= a, m >= b)

# Blocked intervals are given relative to 9:00 (in minutes).
# Margaret's busy times:
busy_margaret = [
    (0, 60),    # 9:00 - 10:00
    (90, 120),  # 10:30 - 11:00
    (150, 180), # 11:30 - 12:00
    (240, 270), # 13:00 - 13:30
    (360, 390)  # 15:00 - 15:30 (won't affect since meeting ends by 13:30)
]

# Donna's busy times:
busy_donna = [
    (330, 360), # 14:30 - 15:00
    (420, 450)  # 16:00 - 16:30
]

# Helen's busy times:
busy_helen = [
    (0, 30),    # 9:00 - 9:30
    (60, 150),  # 10:00 - 11:30
    (240, 300), # 13:00 - 14:00
    (330, 360), # 14:30 - 15:00
    (390, 480)  # 15:30 - 17:00
]

# Add non-overlap constraints for each busy interval of Margaret, Donna, and Helen.
for a, b in busy_margaret:
    s.add(no_overlap(m, a, b))
for a, b in busy_donna:
    s.add(no_overlap(m, a, b))
for a, b in busy_helen:
    s.add(no_overlap(m, a, b))

if s.check() == sat:
    model = s.model()
    meeting_start_offset = model[m].as_long()  # in minutes after 9:00
    meeting_end_offset = meeting_start_offset + duration
    
    # Convert to actual times using the base 9:00.
    actual_start = work_start + meeting_start_offset
    actual_end = work_start + meeting_end_offset
    
    start_time_str = minutes_to_time(actual_start)
    end_time_str = minutes_to_time(actual_end)
    
    # Output in the specified format HH:MM:HH:MM and the day.
    print(f"{start_time_str}:{end_time_str}")
    print("Monday")
else:
    print("No solution found.")