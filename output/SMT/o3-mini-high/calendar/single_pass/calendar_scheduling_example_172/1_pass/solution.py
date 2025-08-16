from z3 import Solver, Int, Or

# Convert time "HH:MM" to minutes since midnight
def to_minutes(hour, minute):
    return hour * 60 + minute

# Meeting details
meeting_duration = 30
work_start = to_minutes(9, 0)    # 09:00 -> 540
work_end   = to_minutes(17, 0)   # 17:00 -> 1020

# Busy intervals for each participant (in minutes)
# Format: (start, end)
patrick_busy = [
    (to_minutes(9, 0), to_minutes(9, 30)),
    (to_minutes(10, 0), to_minutes(10, 30)),
    (to_minutes(13, 30), to_minutes(14, 0)),
    (to_minutes(16, 0), to_minutes(16, 30))
]

kayla_busy = [
    (to_minutes(12, 30), to_minutes(13, 30)),
    (to_minutes(15, 0), to_minutes(15, 30)),
    (to_minutes(16, 0), to_minutes(16, 30))
]

carl_busy = [
    (to_minutes(10, 30), to_minutes(11, 0)),
    (to_minutes(12, 0), to_minutes(12, 30)),
    (to_minutes(13, 0), to_minutes(13, 30)),
    (to_minutes(14, 30), work_end)  # 14:30 to 17:00
]

christian_busy = [
    (to_minutes(9, 0), to_minutes(12, 30)),
    (to_minutes(13, 0), to_minutes(14, 0)),
    (to_minutes(14, 30), work_end)  # 14:30 to 17:00
]

# Initialize the Z3 solver and meeting start variable
s = Solver()
meeting_start = Int('meeting_start')

# Meeting must be within work hours: meeting_start >= 09:00 and meeting_end <= 17:00
s.add(meeting_start >= work_start)
s.add(meeting_start + meeting_duration <= work_end)

# Helper: for each busy interval, ensure meeting does not overlap.
def add_no_overlap_constraint(busy_intervals):
    for (busy_start, busy_end) in busy_intervals:
        # Meeting [meeting_start, meeting_start+meeting_duration) 
        # should be either completely before the busy interval or after it.
        s.add(Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end))

# Add constraints for each participant
add_no_overlap_constraint(patrick_busy)
add_no_overlap_constraint(kayla_busy)
add_no_overlap_constraint(carl_busy)
add_no_overlap_constraint(christian_busy)

# Check for a solution
if s.check() == 'sat':
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration

    # Convert minutes back to HH:MM format
    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    # Since we're scheduling on Monday
    day = "Monday"
    output = f"SOLUTION:\nDay: {day}\nStart Time: {format_time(start_time)}\nEnd Time: {format_time(end_time)}"
    print(output)
else:
    print("No solution found.")