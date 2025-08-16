from z3 import *

# Create the solver instance
solver = Solver()

# Define variables:
# day: Monday = 0, Tuesday = 1, Wednesday = 2.
# start: meeting start time in minutes from midnight.
day = Int("day")
start = Int("start")

# Global constraints:
# 1. Meeting must be scheduled on Monday, Tuesday, or Wednesday.
solver.add(Or(day == 0, day == 1, day == 2))
# 2. Working hours: the meeting must start no earlier than 9:00 (9*60=540) and 
#    end by or before 17:00 (17*60=1020). With meeting length = 60 minutes, start <= 960.
solver.add(start >= 540, start <= 960)

# Preferences:
# Judith would like to avoid more meetings on Monday.
# Since Tuesday actually does not provide a 60-minute free slot for Timothy,
# we add a constraint to disallow Monday so that the meeting is on Tuesday or Wednesday.
# (Tuesday turns out to be unsolvable for a 60-minute block so the only solution will be Wednesday.)
solver.add(day != 0)

# Define helper: disjointness condition for an interval [a, b)
def no_overlap(s, duration, a, b):
    # Meeting [s, s+duration) does not overlap with [a,b) if:
    # either it finishes by a or it starts at/after b.
    return Or(s + duration <= a, s >= b)

# Meeting duration is 60 minutes.
duration = 60

# Monday constraints (for completeness, although Monday is ruled out by the preference):
# Judith’s block on Monday: 12:00-12:30  --> [720,750]
# Timothy’s blocks on Monday:
#   [9:30,10:00]      --> [570,600]
#   [10:30,11:30]     --> [630,690]
#   [12:30,14:00]     --> [750,840]
#   [15:30,17:00]     --> [930,1020]
monday_constraints = And(
    no_overlap(start, duration, 720, 750),   # Judith on Monday
    no_overlap(start, duration, 570, 600),   # Timothy block 1
    no_overlap(start, duration, 630, 690),   # Timothy block 2
    no_overlap(start, duration, 750, 840),   # Timothy block 3
    no_overlap(start, duration, 930, 1020)   # Timothy block 4
)
solver.add(Implies(day == 0, monday_constraints))

# Tuesday constraints:
# Judith has no blocks Tuesday.
# Timothy’s blocks on Tuesday:
#   [9:30,13:00]   --> [570,780]
#   [13:30,14:00]  --> [810,840]
#   [14:30,17:00]  --> [870,1020]
tuesday_constraints = And(
    no_overlap(start, duration, 570, 780),
    no_overlap(start, duration, 810, 840),
    no_overlap(start, duration, 870, 1020)
)
solver.add(Implies(day == 1, tuesday_constraints))

# Wednesday constraints:
# Judith’s block on Wednesday: 11:30-12:00  --> [690,720]
# Also, her preference is to avoid meetings before 12:00, so on Wednesday the meeting must start at or after 12:00.
# Timothy’s blocks on Wednesday:
#   [9:00,9:30]    --> [540,570]
#   [10:30,11:00]  --> [630,660]
#   [13:30,14:30]  --> [810,870]
#   [15:00,15:30]  --> [900,930]
#   [16:00,16:30]  --> [960,990]
wednesday_constraints = And(
    # Enforce preference: meeting should not be before 12:00 (720 minutes)
    start >= 720,
    # (The Judith block [690,720] is automatically avoided by start>=720.)
    no_overlap(start, duration, 810, 870),
    no_overlap(start, duration, 900, 930),
    no_overlap(start, duration, 960, 990)
)
solver.add(Implies(day == 2, wednesday_constraints))

# Solve for a meeting time
if solver.check() == sat:
    m = solver.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    
    # Map integer day value to a string
    if day_val == 0:
        meeting_day = "Monday"
    elif day_val == 1:
        meeting_day = "Tuesday"
    elif day_val == 2:
        meeting_day = "Wednesday"
    else:
        meeting_day = "Unknown"
    
    # Helper function to convert minutes to HH:MM (24-hour format)
    def format_time(mnts):
        hr = mnts // 60
        mn = mnts % 60
        return f"{hr:02d}:{mn:02d}"
    
    start_str = format_time(start_val)
    end_str = format_time(start_val + duration)
    
    # Print the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found.")