from z3 import Solver, Int, Or, And, If, sat

# Create the solver.
s = Solver()

# Define variables:
# day: 0 for Monday, 1 for Tuesday.
# start: meeting start time in minutes offset from 9:00.
day = Int('day')
start = Int('start')
meeting_duration = 60  # meeting duration in minutes

# Ensure day is either Monday (0) or Tuesday (1)
s.add(Or(day == 0, day == 1))

# Working hours: from 9:00 to 17:00.
# start must be chosen so that the meeting finishes by 17:00.
s.add(start >= 0, start + meeting_duration <= 480)  # 480 minutes = 17:00

meeting_end = start + meeting_duration

# Busy intervals expressed as minutes offset from 9:00.
# Monday busy intervals:
#   Alexander: 9:00-11:30 --> (0,150)
#              12:00-14:30 --> (180,330)
#              15:00-17:00 --> (360,480)
#   Russell:   10:30-11:00 --> (90,120)
busy_intervals_monday = [
    (0, 150),    # Alexander
    (180, 330),  # Alexander
    (360, 480),  # Alexander
    (90, 120)    # Russell
]

# Tuesday busy intervals:
#   Alexander: 9:00-10:00   --> (0,60)
#              13:00-14:00  --> (240,300)
#              15:00-15:30  --> (360,390)
#              16:00-16:30  --> (420,450)
#   Russell:   13:00-13:30  --> (240,270)
busy_intervals_tuesday = [
    (0, 60),     # Alexander
    (240, 300),  # Alexander
    (360, 390),  # Alexander
    (420, 450),  # Alexander
    (240, 270)   # Russell
]

# For a meeting and a busy interval [a, b), the meeting does NOT conflict if:
#   meeting_end <= a or start >= b.
def no_conflict(start, meeting_end, interval):
    a, b = interval
    return Or(meeting_end <= a, start >= b)

# Build constraints for each day.
constraints_monday = [no_conflict(start, meeting_end, interval) for interval in busy_intervals_monday]
constraints_tuesday = [no_conflict(start, meeting_end, interval) for interval in busy_intervals_tuesday]

# Russell's preference: on Tuesday, prefer not to meet before 13:30.
# Since 13:30 is 4.5 hours after 9:00, that is 270 minutes.
preference_tuesday = start >= 270

# Add the day-dependent constraints.
s.add(
    If(day == 0,
       And(*constraints_monday),
       And(And(*constraints_tuesday), preference_tuesday)
    )
)

# Check for a solution.
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    
    # Convert the start and end times (offset from 9:00) into HH:MM.
    start_total = chosen_start
    end_total = chosen_start + meeting_duration
    # The actual time is 9:00 plus the offset.
    start_hour = 9 + start_total // 60
    start_min = start_total % 60
    end_hour = 9 + end_total // 60
    end_min = end_total % 60

    # Map day variable to day names.
    day_name = "Monday" if chosen_day == 0 else "Tuesday"
    
    # Format the time range as HH:MM:HH:MM.
    meeting_time = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    
    print(day_name, meeting_time)
else:
    print("No solution found.")