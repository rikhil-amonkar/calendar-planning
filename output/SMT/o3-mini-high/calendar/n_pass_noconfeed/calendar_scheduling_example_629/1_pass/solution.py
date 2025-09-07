from z3 import *

# Helper function: convert minutes since midnight to "HH:MM" string.
def minutes_to_hhmm(m):
    hours = m // 60
    minutes = m % 60
    return "{:02d}:{:02d}".format(hours, minutes)

solver = Solver()

# Define integer variables:
# meeting_start: start time in minutes from midnight.
# day: 0 = Monday, 1 = Tuesday.
meeting_start = Int("meeting_start")
day = Int("day")

duration = 30

# Working hours: meeting must start no earlier than 9:00 (540 minutes)
# and finish by 17:00 (1020 minutes). So meeting_start can be at most 17*60 - duration.
solver.add(meeting_start >= 9 * 60)
solver.add(meeting_start <= (17 * 60 - duration))

# Preference constraints:
# Margaret does not want to meet on Monday => force meeting day to Tuesday.
solver.add(day == 1)
# On Tuesday, Margaret does not want the meeting before 14:30.
solver.add(Implies(day == 1, meeting_start >= (14 * 60 + 30)))  # 14:30 = 870 minutes

# Define busy intervals (in minutes from midnight) for each participant.
# Format: (busy_start, busy_end)
# Margaret's busy intervals:
busy_Margaret_Mon = [(10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 17 * 60)]
busy_Margaret_Tue = [(12 * 60, 12 * 60 + 30)]
# Alexis's busy intervals:
busy_Alexis_Mon = [(9 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (14 * 60, 17 * 60)]
busy_Alexis_Tue = [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (14 * 60, 16 * 60 + 30)]

# For a meeting [meeting_start, meeting_start+duration) to be valid,
# it must not intersect any busy interval.
def no_overlap(meet_start, busy_start, busy_end):
    # Either the meeting ends at or before the busy interval starts
    # or starts at or after the busy interval ends.
    return Or(meet_start + duration <= busy_start, meet_start >= busy_end)

# Apply busy constraints conditionally for each day.
# Monday constraints (won't matter since day==1, but added for completeness):
for b_start, b_end in busy_Margaret_Mon:
    solver.add(Implies(day == 0, no_overlap(meeting_start, b_start, b_end)))
for b_start, b_end in busy_Alexis_Mon:
    solver.add(Implies(day == 0, no_overlap(meeting_start, b_start, b_end)))

# Tuesday constraints:
for b_start, b_end in busy_Margaret_Tue:
    solver.add(Implies(day == 1, no_overlap(meeting_start, b_start, b_end)))
for b_start, b_end in busy_Alexis_Tue:
    solver.add(Implies(day == 1, no_overlap(meeting_start, b_start, b_end)))

# Notice: For Tuesday, Alexis has a busy interval from 14:00 to 16:30.
# Given the preference meeting_start >= 14:30, the meeting would only fit if it
# starts after Alexis’s meeting, i.e. meeting_start >= 16*60 + 30 = 990.
solver.add(Implies(day == 1, meeting_start >= (16 * 60 + 30)))  # meeting_start must be >= 990

if solver.check() == sat:
    model = solver.model()
    chosen_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    start = model[meeting_start].as_long()
    end = start + duration
    # Format output as HH:MM:HH:MM and include the day of the week.
    print("Meeting Day:", chosen_day)
    print("Meeting Time:", minutes_to_hhmm(start) + ":" + minutes_to_hhmm(end))
else:
    print("No solution found.")