from z3 import Solver, Int, Or

# We'll represent times in minutes from midnight.
# For example, 9:00 is 9*60 = 540 and 17:00 is 1020. 
# Note: Juan cannot have meetings after 16:00 (i.e. meeting must finish by 16:00 = 960 minutes).

s = Solver()

# Define meeting start time as an integer (minutes) and the meeting has a fixed duration of 30 minutes.
meeting_start = Int('meeting_start')
meeting_end = meeting_start + 30

# Add basic constraints:
# 1. The meeting must start no earlier than 9:00.
# 2. The meeting must finish by 16:00 because Juan cannot meet after 16:00.
s.add(meeting_start >= 9 * 60)         # 9:00 -> 540 minutes
s.add(meeting_end <= 16 * 60)            # 16:00 -> 960 minutes

# Define a helper to ensure the meeting interval does NOT overlap a busy interval.
# The meeting [M_start, M_end) does not conflict with a busy interval [B_start, B_end)
# if either the meeting ends on or before B_start or it starts on or after B_end.
def no_overlap(m_start, m_end, b_start, b_end):
    return Or(m_end <= b_start, m_start >= b_end)

# Add constraints for each participant's busy intervals.
# Times are in minutes from midnight.

# Juan's busy intervals: 9:00-10:30 and 15:30-16:00.
s.add(no_overlap(meeting_start, meeting_end, 9 * 60, 10 * 60 + 30))    # [540, 630]
s.add(no_overlap(meeting_start, meeting_end, 15 * 60 + 30, 16 * 60))   # [930, 960]

# Marilyn's busy intervals: 11:00-11:30 and 12:30-13:00.
s.add(no_overlap(meeting_start, meeting_end, 11 * 60, 11 * 60 + 30))    # [660, 690]
s.add(no_overlap(meeting_start, meeting_end, 12 * 60 + 30, 13 * 60))    # [750, 780]

# Ronald's busy intervals: 9:00-10:30, 12:00-12:30, 13:00-13:30, and 14:00-16:30.
s.add(no_overlap(meeting_start, meeting_end, 9 * 60, 10 * 60 + 30))      # [540, 630]
s.add(no_overlap(meeting_start, meeting_end, 12 * 60, 12 * 60 + 30))     # [720, 750]
s.add(no_overlap(meeting_start, meeting_end, 13 * 60, 13 * 60 + 30))     # [780, 810]
s.add(no_overlap(meeting_start, meeting_end, 14 * 60, 16 * 60 + 30))     # [840, 990]

# Check the constraints for a solution.
if s.check() == sat:
    m = s.model()
    start = m[meeting_start].as_long()
    end = start + 30
    # Convert minutes back to HH:MM format.
    start_hour = start // 60
    start_minute = start % 60
    end_hour = end // 60
    end_minute = end % 60
    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    
    # Output the solution as required.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + start_str)
    print("End Time: " + end_str)
else:
    print("No solution found with the given constraints.")