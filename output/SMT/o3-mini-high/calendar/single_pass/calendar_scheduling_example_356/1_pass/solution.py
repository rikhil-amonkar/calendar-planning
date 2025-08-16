from z3 import Int, Solver, Or, sat

# Helper function to convert minutes since midnight to HH:MM format.
def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting duration is 30 minutes.
duration = 30

# Work hours are 9:00 to 17:00.
start_of_day = 9 * 60    # 9:00 in minutes (540)
end_of_day = 17 * 60     # 17:00 in minutes (1020)

s = Solver()
# Define the meeting start time (in minutes from midnight)
meeting_start = Int('meeting_start')

# The meeting must lie fully within work hours.
s.add(meeting_start >= start_of_day)
s.add(meeting_start + duration <= end_of_day)

# Angela would like to avoid meetings before 15:00.
s.add(meeting_start >= 15 * 60)  # 15:00 is 900 minutes

# A helper to enforce that the 30-minute meeting does not overlap a busy interval.
def no_conflict(busy_start, busy_end):
    # Either the meeting ends at or before the busy period starts,
    # or it starts at or after the busy period ends.
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

# Katherine's busy times:
#   12:00 to 12:30 and 13:00 to 14:30.
s.add(no_conflict(12 * 60, 12 * 60 + 30))   # 12:00 to 12:30 -> [720,750)
s.add(no_conflict(13 * 60, 14 * 60 + 30))     # 13:00 to 14:30 -> [780,870)

# Rebecca has no meetings.

# Julie's busy times:
#   9:00 to 9:30, 10:30 to 11:00, 13:30 to 14:00, 15:00 to 15:30.
s.add(no_conflict(9 * 60, 9 * 60 + 30))         # 9:00 to 9:30 -> [540,570)
s.add(no_conflict(10 * 60 + 30, 11 * 60))       # 10:30 to 11:00 -> [630,660)
s.add(no_conflict(13 * 60 + 30, 14 * 60))       # 13:30 to 14:00 -> [810,840)
s.add(no_conflict(15 * 60, 15 * 60 + 30))       # 15:00 to 15:30 -> [900,930)

# Angela's busy times:
#   9:00 to 10:00, 10:30 to 11:00, 11:30 to 14:00, 
#   14:30 to 15:00, 16:30 to 17:00.
s.add(no_conflict(9 * 60, 10 * 60))             # 9:00 to 10:00 -> [540,600)
s.add(no_conflict(10 * 60 + 30, 11 * 60))       # 10:30 to 11:00 -> [630,660)
s.add(no_conflict(11 * 60 + 30, 14 * 60))       # 11:30 to 14:00 -> [690,840)
s.add(no_conflict(14 * 60 + 30, 15 * 60))       # 14:30 to 15:00 -> [870,900)
s.add(no_conflict(16 * 60 + 30, 17 * 60))       # 16:30 to 17:00 -> [990,1020)

# Nicholas's busy times:
#   9:30 to 11:00, 11:30 to 13:30, 14:00 to 16:00, 16:30 to 17:00.
s.add(no_conflict(9 * 60 + 30, 11 * 60))        # 9:30 to 11:00 -> [570,660)
s.add(no_conflict(11 * 60 + 30, 13 * 60 + 30))  # 11:30 to 13:30 -> [690,810)
s.add(no_conflict(14 * 60, 16 * 60))            # 14:00 to 16:00 -> [840,960)
s.add(no_conflict(16 * 60 + 30, 17 * 60))       # 16:30 to 17:00 -> [990,1020)

# Carl's busy times:
#   9:00 to 11:00, 11:30 to 12:30, 13:00 to 14:30, 15:00 to 16:00, 16:30 to 17:00.
s.add(no_conflict(9 * 60, 11 * 60))             # 9:00 to 11:00 -> [540,660)
s.add(no_conflict(11 * 60 + 30, 12 * 60 + 30))   # 11:30 to 12:30 -> [690,750)
s.add(no_conflict(13 * 60, 14 * 60 + 30))        # 13:00 to 14:30 -> [780,870)
s.add(no_conflict(15 * 60, 16 * 60))             # 15:00 to 16:00 -> [900,960)
s.add(no_conflict(16 * 60 + 30, 17 * 60))        # 16:30 to 17:00 -> [990,1020)

if s.check() == sat:
    m = s.model()
    start = m[meeting_start].as_long()
    end = start + duration

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", minutes_to_time(start))
    print("End Time:", minutes_to_time(end))
else:
    print("No solution found")