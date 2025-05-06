from z3 import *

# Helper function: Convert a time string "HH:MM" to minutes after midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Meeting configuration
meeting_duration = 30  # 30 minutes meeting

# Workday boundaries (for both days)
work_start = time_to_minutes("9:00")   # 540 minutes
work_end   = time_to_minutes("17:00")  # 1020 minutes

# Harold's busy intervals on Monday and Tuesday:
# Monday busy intervals for Harold:
monday_events = [
    (time_to_minutes("9:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("17:00"))
]
# Tuesday busy intervals for Harold:
tuesday_events = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Jeffrey has no meetings during the week.

# Create a Z3 solver instance.
s = Solver()

# meeting_start is an integer variable representing the start time in minutes.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# day variable: 0 represents Monday, 1 represents Tuesday.
day = Int("day")
s.add(Or(day == 0, day == 1))  # day must be either Monday or Tuesday

# Common constraints: meeting must be within work hours.
s.add(meeting_start >= work_start)
s.add(meeting_end <= work_end)

# Add day-specific constraints:
# For Monday: the meeting must not overlap any of Monday busy intervals.
for (start_busy, end_busy) in monday_events:
    s.add(Implies(day == 0, Or(meeting_end <= start_busy, meeting_start >= end_busy)))

# For Tuesday: the meeting must not overlap any of Tuesday busy intervals.
for (start_busy, end_busy) in tuesday_events:
    s.add(Implies(day == 1, Or(meeting_end <= start_busy, meeting_start >= end_busy)))
# And Harold would like the meeting to be scheduled Tuesday before 14:30 if on Tuesday.
s.add(Implies(day == 1, meeting_end <= time_to_minutes("14:30")))

# Check if a solution exists.
if s.check() == sat:
    model = s.model()
    chosen_day = model[day].as_long()
    start = model[meeting_start].as_long()
    end = start + meeting_duration

    # Helper function to convert minutes to HH:MM format.
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    day_str = "Monday" if chosen_day == 0 else "Tuesday"
    print("A possible meeting time:")
    print(f"Day:   {day_str}")
    print(f"Start: {minutes_to_time(start)}")
    print(f"End:   {minutes_to_time(end)}")
else:
    print("No valid meeting time could be found.")