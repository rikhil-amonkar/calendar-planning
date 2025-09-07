from z3 import Solver, Int, Or

# Meeting parameters
MEETING_DURATION = 30  # in minutes
WORK_START = 9 * 60    # 9:00 in minutes
WORK_END = 17 * 60     # 17:00 in minutes

# Define the meeting start time as an integer (minutes after midnight)
meeting_start = Int('meeting_start')

# Create the solver and add the work hours constraints:
s = Solver()
s.add(meeting_start >= WORK_START)
s.add(meeting_start + MEETING_DURATION <= WORK_END)

# Define busy intervals for each participant (start, end) in minutes
# Ronald's calendar is free so we don't add any constraints for him.
busy_intervals = [
    # Stephen's busy intervals: 10:00-10:30, 12:00-12:30
    (10 * 60, 10 * 60 + 30),
    (12 * 60, 12 * 60 + 30),
    
    # Brittany's busy intervals: 11:00-11:30, 13:30-14:00, 15:30-16:00, 16:30-17:00
    (11 * 60, 11 * 60 + 30),
    (13 * 60 + 30, 13 * 60 + 60),
    (15 * 60 + 30, 16 * 60),
    (16 * 60 + 30, 17 * 60),
    
    # Dorothy's busy intervals: 9:00-9:30, 10:00-10:30, 11:00-12:30, 13:00-15:00, 15:30-17:00
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 10 * 60 + 30),
    (11 * 60, 12 * 60 + 30),
    (13 * 60, 15 * 60),
    (15 * 60 + 30, 17 * 60),
    
    # Rebecca's busy intervals: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-17:00
    (9 * 60 + 30, 10 * 60 + 30),
    (11 * 60, 11 * 60 + 30),
    (12 * 60, 12 * 60 + 30),
    (13 * 60, 17 * 60),
    
    # Jordan's busy intervals: 9:00-9:30, 10:00-11:00, 11:30-12:00, 13:00-15:00, 15:30-16:30
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 11 * 60),
    (11 * 60 + 30, 12 * 60),
    (13 * 60, 15 * 60),
    (15 * 60 + 30, 16 * 60 + 30)
]

# For each busy interval, ensure the meeting does not overlap with it.
# This is expressed as: meeting ends at or before the busy interval starts, 
# or meeting starts on or after the busy interval ends.
for (busy_start, busy_end) in busy_intervals:
    s.add(Or(meeting_start + MEETING_DURATION <= busy_start, meeting_start >= busy_end))

# Check for a solution.
if s.check() == 'sat':
    m = s.model()
    start = m[meeting_start].as_long()
    end = start + MEETING_DURATION
    
    # Convert minutes to HH:MM format
    start_hour = start // 60
    start_minute = start % 60
    end_hour = end // 60
    end_minute = end % 60
    
    # Output the scheduled meeting time and the day of the week.
    print("Monday")
    print("{:02d}:{:02d}:{:02d}:{:02d}".format(start_hour, start_minute, end_hour, end_minute))
else:
    print("No solution found")