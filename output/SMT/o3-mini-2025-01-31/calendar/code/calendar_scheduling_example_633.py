from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters:
duration = 60  # duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes from midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)
solver.add(Or(day == 0, day == 1))

# Additional constraint for Carolyn:
# Carolyn would rather not meet on Monday after 12:30.
# For Monday (day == 0), the meeting must end by 12:30, i.e., start + duration <= 750.
solver.add(Implies(day == 0, start + duration <= 750))

# Busy schedules:
# Lisa's busy times:
#   Tuesday: 10:00 to 10:30 -> (600, 630)
#            13:30 to 14:00 -> (810, 840)
lisa_tuesday_busy = [
    (600, 630),
    (810, 840)
]

# Carolyn's busy times:
#   Monday:
#       12:00 to 12:30 -> (720, 750)
#       13:30 to 14:00 -> (810, 840)
#       14:30 to 15:30 -> (870, 930)
#       16:00 to 16:30 -> (960, 990)
carolyn_monday_busy = [
    (720, 750),
    (810, 840),
    (870, 930),
    (960, 990)
]
#   Tuesday:
#       9:00 to 10:30 -> (540, 630)
#       11:00 to 11:30 -> (660, 690)
#       12:00 to 14:00 -> (720, 840)
#       14:30 to 15:00 -> (870, 900)
#       15:30 to 16:30 -> (930, 990)
carolyn_tuesday_busy = [
    (540, 630),
    (660, 690),
    (720, 840),
    (870, 900),
    (930, 990)
]

# Helper function: meeting interval [start, start+duration) must not overlap busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add Lisa's busy constraints for Tuesday:
for b_start, b_end in lisa_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))
    
# Carolyn's busy constraints on Monday:
for b_start, b_end in carolyn_monday_busy:
    solver.add(Implies(day == 0, non_overlap(b_start, b_end)))

# Carolyn's busy constraints on Tuesday:
for b_start, b_end in carolyn_tuesday_busy:
    solver.add(Implies(day == 1, non_overlap(b_start, b_end)))

# Search for a valid meeting time by iterating over possible start times (in minutes) within work hours.
found = False
meeting_start = None
meeting_day = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_day = model[day].as_long()  # 0: Monday, 1: Tuesday
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = meeting_start + duration
    s_hour, s_min = divmod(meeting_start, 60)
    e_hour, e_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {s_hour:02d}:{s_min:02d} to {e_hour:02d}:{e_min:02d}.")
else:
    print("No valid meeting time could be found.")