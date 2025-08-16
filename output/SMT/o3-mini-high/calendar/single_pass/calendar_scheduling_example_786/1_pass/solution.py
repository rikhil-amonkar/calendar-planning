from z3 import *

# Create a solver instance
s = Solver()

# Define integer variables:
# day: 0=Monday, 1=Tuesday, 2=Wednesday.
day = Int('day')
# meeting_start: minutes from midnight.
meeting_start = Int('meeting_start')
meeting_duration = 30
meeting_end = meeting_start + meeting_duration

# Work hour boundaries in minutes: 9:00 = 540, 17:00 = 1020.
s.add(Or(day == 0, day == 1, day == 2))
s.add(meeting_start >= 540, meeting_start <= 1020 - meeting_duration)

# Pamela's preferences:
# "would like to avoid more meetings on Monday, Tuesday, and Wednesday before 16:00"
# We enforce these as hard constraints so that the meeting is not on Monday or Tuesday,
# and if on Wednesday the meeting must start no earlier than 16:00 (16:00 = 960 minutes).
s.add(day == 2)
s.add(Implies(day == 2, meeting_start >= 960))

# Helper: Defines the condition that the meeting [start, end) does NOT overlap a busy interval [b_start, b_end)
def no_overlap(start, end, b_start, b_end):
    return Or(end <= b_start, start >= b_end)

# Busy intervals for Amy:
# Amy is busy on Wednesday (day 2) during:
#  11:00 to 11:30  => [660, 690] minutes
#  13:30 to 14:00  => [810, 840] minutes
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 660, 690)))
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 810, 840)))

# Busy intervals for Pamela:
# Monday (day 0): busy 9:00-10:30 and 11:00-16:30
#   → [540, 630] and [660, 990]
s.add(Implies(day == 0, no_overlap(meeting_start, meeting_end, 540, 630)))
s.add(Implies(day == 0, no_overlap(meeting_start, meeting_end, 660, 990)))

# Tuesday (day 1): busy 9:00-9:30 and 10:00-17:00
#   → [540, 570] and [600, 1020]
s.add(Implies(day == 1, no_overlap(meeting_start, meeting_end, 540, 570)))
s.add(Implies(day == 1, no_overlap(meeting_start, meeting_end, 600, 1020)))

# Wednesday (day 2): busy 9:00-9:30, 10:00-11:00, 11:30-13:30,
#                      14:30-15:00, and 16:00-16:30
#   → [540,570], [600,660], [690,810], [870,900], [960,990]
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 540, 570)))
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 600, 660)))
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 690, 810)))
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 870, 900)))
s.add(Implies(day == 2, no_overlap(meeting_start, meeting_end, 960, 990)))

# Solve the scheduling problem
if s.check() == sat:
    m = s.model()
    # Map the day integer back to a day name
    day_str = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    chosen_day = day_str[m[day].as_long()]
    start_val = m[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Convert minutes to HH:MM format
    def minutes_to_time(mnts):
        hour = mnts // 60
        minute = mnts % 60
        return f"{hour:02d}:{minute:02d}"

    start_time_str = minutes_to_time(start_val)
    end_time_str = minutes_to_time(end_val)

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day:", chosen_day)
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution found.")