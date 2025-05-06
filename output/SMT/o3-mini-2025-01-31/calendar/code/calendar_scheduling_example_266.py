from z3 import Optimize, Int, Or, sat

# Helper functions to convert time strings
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration
meeting_duration = 30  # meeting duration in minutes
work_start = time_to_minutes("9:00")   # 9:00 AM
work_end   = time_to_minutes("17:00")   # 5:00 PM

# Busy intervals for each participant (in minutes)
# Joe's busy intervals
joe_busy = [
    (time_to_minutes("9:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00"))
]

# Keith's busy intervals
keith_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Patricia's busy intervals
patricia_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30"))
]

# Nancy's busy intervals
nancy_busy = [
    (time_to_minutes("9:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("16:30"))
]

# Pamela's busy intervals
pamela_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Create a Z3 Optimize solver.
opt = Optimize()

# Decision variable for the meeting start time (in minutes from midnight on Monday).
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Add constraint: meeting must be within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Helper function to ensure no overlap with busy intervals.
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting must end before a busy interval starts OR start after it ends.
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))

# Add constraints for each participant.
add_busy_constraints(joe_busy)
add_busy_constraints(keith_busy)
add_busy_constraints(patricia_busy)
add_busy_constraints(nancy_busy)
add_busy_constraints(pamela_busy)

# Objective: minimize the meeting start time (schedule it as early as possible)
opt.minimize(meeting_start)

# Check for a viable meeting time.
if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_val))
    print("End:  ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")