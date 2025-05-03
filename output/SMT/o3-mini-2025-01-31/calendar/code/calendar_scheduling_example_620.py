from z3 import Solver, Int, Or, Implies, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes after midnight
day = Int("day")      # day: 0 for Monday, 1 for Tuesday

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Create a Z3 solver and add the basic constraints:
solver = Solver()
solver.add(start >= WORK_START, start + duration <= WORK_END)

# Since Maria does not want to meet on Tuesday, we force the meeting to be on Monday.
solver.add(day == 0)

# Define busy intervals in minutes:
# Christopher's busy schedule:
# Monday:
#   16:00 to 16:30 -> (960, 990)
christopher_monday_busy = [(960, 990)]
# (Tuesday busy not needed because meeting is forced to Monday)

# Maria's busy schedule (Monday):
#   9:00 to 9:30   -> (540, 570)
#   10:00 to 10:30  -> (600, 630)
#   11:00 to 11:30  -> (660, 690)
#   12:00 to 12:30  -> (720, 750)
#   14:00 to 14:30  -> (840, 870)
#   15:00 to 15:30  -> (900, 930)
#   16:30 to 17:00  -> (990, 1020)
maria_monday_busy = [
    (540, 570),
    (600, 630),
    (660, 690),
    (720, 750),
    (840, 870),
    (900, 930),
    (990, 1020)
]

# Define a helper function that states the meeting [start, start+duration) does NOT overlap
# with a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Add constraints for Christopher's busy schedule on Monday
for b_start, b_end in christopher_monday_busy:
    solver.add(non_overlap(b_start, b_end))

# Add constraints for Maria's busy schedule on Monday
for b_start, b_end in maria_monday_busy:
    solver.add(non_overlap(b_start, b_end))

# We want the meeting at the earliest availability on Monday.
found = False
meeting_start = None

for t in range(WORK_START, WORK_END - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        found = True
        solver.pop()
        break
    solver.pop()

if found:
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print(f"A valid meeting time is on Monday from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found.")