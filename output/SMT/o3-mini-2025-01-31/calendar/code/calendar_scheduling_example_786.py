from z3 import *

# Helper functions to convert between time strings and minutes.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # half an hour meeting.
work_start = time_to_minutes("9:00")    # 540 minutes.
work_end   = time_to_minutes("17:00")   # 1020 minutes.

# Create a Z3 solver instance.
s = Solver()

# We'll represent days as integers: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
meeting_day = Int("meeting_day")
s.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))

# Pamela's preferences:
#   - Avoid meetings on Monday.
#   - Avoid meetings on Tuesday.
#   - Avoid meetings on Wednesday that start before 16:00.
# Enforced as hard constraints, so the meeting must be on Wednesday and,
# if on Wednesday, start no earlier than 16:00.
s.add(meeting_day != 0, meeting_day != 1)
preferred_wed_start = time_to_minutes("16:00")
    
# Declare the meeting start time (in minutes) and compute its end.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constraint 1: Meeting must fall within the workday regardless of the day.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint 2: If the meeting is on Wednesday, it should not start before the preferred time.
s.add(Implies(meeting_day == 2, meeting_start >= preferred_wed_start))

# Participant busy schedules are applied only on the day the meeting occurs.

# Amy's busy intervals (only provided for Wednesday).
amy_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00"))
]
for busy_start, busy_end in amy_busy:
    s.add(Implies(meeting_day == 2,
                  Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Pamela's busy intervals.
# Monday and Tuesday intervals are not relevant due to her preference, so consider Wednesday only.
pamela_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("9:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]
for busy_start, busy_end in pamela_busy:
    s.add(Implies(meeting_day == 2,
                  Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Check for a meeting time that satisfies all constraints.
if s.check() == sat:
    model = s.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}[day_val]
    
    print("A possible meeting time:")
    print(f"Day:   {day_str}")
    print(f"Start: {minutes_to_time(start_val)}")
    print(f"End:   {minutes_to_time(end_val)}")
else:
    print("No valid meeting time could be found.")