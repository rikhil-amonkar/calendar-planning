from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting lasts 30 minutes
work_start = 9 * 60      # 9:00 in minutes (540)
work_end   = 17 * 60     # 17:00 in minutes (1020)

# Create an integer variable for the meeting start time (in minutes from midnight)
meetingStart = Int('meetingStart')
meetingEnd = meetingStart + duration

s = Solver()

# Working hours constraint: meeting must be entirely within 9:00 to 17:00
s.add(meetingStart >= work_start)
s.add(meetingEnd <= work_end)

# Harold’s preference: meeting must be scheduled entirely before 13:00.
# That is, the meeting must finish by 13:00 (13*60 = 780), so meetingStart <= 750.
s.add(meetingStart <= (13 * 60 - duration))

# Busy intervals for each participant (times in minutes from midnight):
# Jacqueline: blocked 9:00-9:30, 11:00-11:30, 12:30-13:00, 15:30-16:00
busy_jacqueline = [(540, 570), (660, 690), (750, 780), (930, 960)]
# Harold: busy 10:00-10:30, 13:00-13:30, 15:00-17:00
busy_harold     = [(600, 630), (780, 810), (900, 1020)]
# Arthur: busy 9:00-9:30, 10:00-12:30, 14:30-15:00, 15:30-17:00
busy_arthur     = [(540, 570), (600, 750), (870, 900), (930, 1020)]
# Kelly: busy 9:00-9:30, 10:00-11:00, 11:30-12:30, 14:00-15:00, 15:30-16:00
busy_kelly      = [(540, 570), (600, 660), (690, 750), (840, 900), (930, 960)]

# Combine all busy intervals
busy_intervals = busy_jacqueline + busy_harold + busy_arthur + busy_kelly

# For each busy interval, ensure that the meeting does not overlap with it.
# The meeting (meetingStart, meetingEnd) must either finish before the busy interval starts,
# or start after the busy interval ends.
for (busy_start, busy_end) in busy_intervals:
    s.add(Or(meetingEnd <= busy_start, meetingStart >= busy_end))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    start_time_val = m[meetingStart].as_long()
    end_time_val = start_time_val + duration

    # Utility to format minutes into HH:MM (24-hour format)
    def format_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = format_time(start_time_val)
    end_str = format_time(end_time_val)
    
    # Output the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", start_str)
    print("End Time:", end_str)
else:
    print("No solution found.")