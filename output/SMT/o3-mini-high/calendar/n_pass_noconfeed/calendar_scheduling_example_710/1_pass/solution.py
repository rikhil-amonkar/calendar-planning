from z3 import Solver, Int, Or, Implies, sat

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Create the solver
s = Solver()

# Define meeting variables:
# day: 0 for Monday, 1 for Tuesday (Cheryl cannot meet on Wednesday)
# start: meeting start time in minutes (from midnight)
day = Int("day")
start = Int("start")
meeting_duration = 30

# Working day constraints: meeting must be scheduled between 9:00 and 17:00.
# So start must be between 9:00 (540 minutes) and 16:30 (990 minutes)
s.add(Or(day == 0, day == 1))  # Only Monday (0) or Tuesday (1)
s.add(start >= 9 * 60, start <= 17 * 60 - meeting_duration)

# Define busy intervals for each participant as tuples: (day, start_minute, end_minute)

# Cheryl's busy schedule
cheryl_busy = [
    (0, 9 * 60, 9 * 60 + 30),      # Monday: 9:00 - 9:30
    (0, 11 * 60 + 30, 13 * 60),     # Monday: 11:30 - 13:00
    (0, 15 * 60 + 30, 16 * 60),     # Monday: 15:30 - 16:00
    (1, 15 * 60, 15 * 60 + 30)      # Tuesday: 15:00 - 15:30
]

# Kyle's busy schedule
kyle_busy = [
    (0, 9 * 60, 17 * 60),          # Monday: 9:00 - 17:00
    (1, 9 * 60 + 30, 17 * 60)       # Tuesday: 9:30 - 17:00
    # Note: Kyle's Wednesday busy intervals are not needed because Cheryl cannot meet on Wednesday.
]

# Function to ensure the meeting does not overlap with a busy interval.
def no_overlap(meeting_day, meeting_start, duration, busy_day, busy_start, busy_end):
    meeting_end = meeting_start + duration
    # If the meeting is on the same day as the busy slot then it must end before the busy starts
    # or start after the busy ends.
    return Implies(meeting_day == busy_day, Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add constraints for Cheryl's busy intervals.
for b_day, b_start, b_end in cheryl_busy:
    s.add(no_overlap(day, start, meeting_duration, b_day, b_start, b_end))

# Add constraints for Kyle's busy intervals.
for b_day, b_start, b_end in kyle_busy:
    s.add(no_overlap(day, start, meeting_duration, b_day, b_start, b_end))

# Check for a feasible solution.
if s.check() == sat:
    model = s.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Map day integer to a weekday name.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_names[meeting_day]
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output the proposed meeting time.
    print(f"{day_str} {start_str}:{end_str}")
else:
    print("No solution found.")