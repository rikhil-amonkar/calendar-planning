from z3 import *

# We represent the meeting day as an integer:
#   0 = Monday, 1 = Tuesday, 2 = Wednesday.
# The meeting start time is measured in minutes from midnight.
# Work hours are 9:00 (540 minutes) to 17:00 (1020 minutes).
# The meeting duration is 60 minutes.

s = Solver()

# Decision variables:
day = Int('day')
start = Int('start')  # start time in minutes from midnight
duration = 60
end = start + duration

# The meeting must happen within work hours.
s.add(start >= 540, end <= 1020)

# The meeting day must be one of Monday (0), Tuesday (1), or Wednesday (2).
s.add(Or(day == 0, day == 1, day == 2))
# Stephanie prefers to avoid Monday, and since there is another valid day, we rule it out.
s.add(day != 0)

# Betty’s extra constraint: on Tuesday, she cannot meet after 12:30.
# 12:30 is 750 minutes; the meeting (if on Tuesday) must finish by then.
s.add(Implies(day == 1, end <= 750))

# To avoid scheduling conflicts with existing meetings,
# for any meeting on a given day, our meeting (interval [start, end)) must not overlap it.
# Two intervals [A,B) and [C,D) do not overlap if either B <= C or A >= D.

# --- Stephanie's Meetings ---
# Monday (day 0) meetings:
#   9:30-10:00  -> [570, 600)
s.add(Implies(day == 0, Or(end <= 570, start >= 600)))
#   10:30-11:00 -> [630, 660)
s.add(Implies(day == 0, Or(end <= 630, start >= 660)))
#   11:30-12:00 -> [690, 720)
s.add(Implies(day == 0, Or(end <= 690, start >= 720)))
#   14:00-14:30 -> [840, 870)
s.add(Implies(day == 0, Or(end <= 840, start >= 870)))

# Tuesday (day 1) meeting:
#   12:00-13:00 -> [720, 780)
s.add(Implies(day == 1, Or(end <= 720, start >= 780)))

# Wednesday (day 2) meetings:
#   9:00-10:00   -> [540, 600)
s.add(Implies(day == 2, Or(end <= 540, start >= 600)))
#   13:00-14:00  -> [780, 840)
s.add(Implies(day == 2, Or(end <= 780, start >= 840)))

# --- Betty's Meetings ---
# Monday (day 0) meetings:
#   9:00-10:00   -> [540, 600)
s.add(Implies(day == 0, Or(end <= 540, start >= 600)))
#   11:00-11:30  -> [660, 690)
s.add(Implies(day == 0, Or(end <= 660, start >= 690)))
#   14:30-15:00  -> [870, 900)
s.add(Implies(day == 0, Or(end <= 870, start >= 900)))
#   15:30-16:00  -> [930, 960)
s.add(Implies(day == 0, Or(end <= 930, start >= 960)))

# Tuesday (day 1) meetings:
#   9:00-9:30    -> [540, 570)
s.add(Implies(day == 1, Or(end <= 540, start >= 570)))
#   11:30-12:00  -> [690, 720)
s.add(Implies(day == 1, Or(end <= 690, start >= 720)))
#   12:30-14:30  -> [750, 870)
# (This one is automatically satisfied by Betty’s Tuesday end constraint, but we add it for completeness.)
s.add(Implies(day == 1, Or(end <= 750, start >= 870)))
#   15:30-16:00  -> [930, 960)
s.add(Implies(day == 1, Or(end <= 930, start >= 960)))

# Wednesday (day 2) meetings:
#   10:00-11:30  -> [600, 690)
s.add(Implies(day == 2, Or(end <= 600, start >= 690)))
#   12:00-14:00  -> [720, 840)
s.add(Implies(day == 2, Or(end <= 720, start >= 840)))
#   14:30-17:00  -> [870, 1020)
s.add(Implies(day == 2, Or(end <= 870, start >= 1020)))

# Try to find a solution.
if s.check() == sat:
    m = s.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + duration

    # Map the integer day to its string representation.
    day_str = ["Monday", "Tuesday", "Wednesday"][day_val]

    # Convert a time in minutes to a string in HH:MM format.
    def minutes_to_timestr(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = minutes_to_timestr(start_val)
    end_str = minutes_to_timestr(end_val)

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found.")