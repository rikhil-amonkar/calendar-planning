from z3 import Solver, Int, Or, sat

def minutes_to_hhmm(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Constants for meeting scheduling
duration = 30  # Meeting duration in minutes
start_work = 9 * 60    # 9:00 in minutes (540)
end_work = 17 * 60     # 17:00 in minutes (1020)

# Create an SMT solver instance
s = Solver()

# Define the meeting start time as an integer (minutes from midnight)
m = Int('m')
meeting_end = m + duration

# Meeting must start and end within work hours
s.add(m >= start_work, meeting_end <= end_work)

# Define all blocked intervals for each participant (in minutes)
# Times are given as (start, end)
blocked_intervals = [
    # Bradley's blocked times
    (570, 600),   # 9:30 to 10:00
    (750, 780),   # 12:30 to 13:00
    (810, 840),   # 13:30 to 14:00
    (930, 960),   # 15:30 to 16:00

    # Teresa's blocked times
    (630, 660),   # 10:30 to 11:00
    (720, 750),   # 12:00 to 12:30
    (780, 810),   # 13:00 to 13:30
    (870, 900),   # 14:30 to 15:00

    # Elizabeth's blocked times
    (540, 570),   # 9:00 to 9:30
    (630, 690),   # 10:30 to 11:30
    (780, 810),   # 13:00 to 13:30
    (870, 900),   # 14:30 to 15:00
    (930, 1020),  # 15:30 to 17:00

    # Christian's blocked times
    (540, 570),   # 9:00 to 9:30
    (630, 1020)   # 10:30 to 17:00
]

# For each blocked interval, ensure that the meeting does NOT overlap.
# That is, the meeting must end before a blocked interval starts,
# or it must start after a blocked interval ends.
for (b_start, b_end) in blocked_intervals:
    s.add( Or(meeting_end <= b_start, m >= b_end) )

# Check if there is a valid meeting time
if s.check() == sat:
    model = s.model()
    meeting_start_val = model[m].as_long()
    meeting_end_val = meeting_start_val + duration
    start_str = minutes_to_hhmm(meeting_start_val)
    end_str = minutes_to_hhmm(meeting_end_val)
    # Output the meeting time along with the day of the week
    print(f"Monday {start_str}:{end_str}")
else:
    print("No meeting time found.")