from z3 import Solver, Int, Or, sat

# Meeting duration (30 minutes)
duration = 30

# Meeting start variable is represented in minutes after midnight.
start = Int("start")

# Define work hours in minutes (9:00=540, 17:00=1020)
WORK_START = 540
WORK_END = 1020

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
candidate_days = [0, 1, 2]

# Joshua's busy schedule (times in minutes after midnight):
# Monday:
#    15:00 to 15:30 -> (900, 930)
# Tuesday:
#    11:30 to 12:00 -> (690, 720)
#    13:00 to 13:30 -> (780, 810)
#    14:30 to 15:00 -> (870, 900)
# Wednesday:
#    (No meetings for Joshua on Wednesday)
joshua_busy = {
    0: [(900, 930)],
    1: [(690, 720), (780, 810), (870, 900)],
    2: []
}

# Joyce's busy schedule:
# Monday:
#    9:00 to 9:30  -> (540, 570)
#    10:00 to 11:00 -> (600, 660)
#    11:30 to 12:30 -> (690, 750)
#    13:00 to 15:00 -> (780, 900)
#    15:30 to 17:00 -> (930, 1020)
# Tuesday:
#    9:00 to 17:00  -> (540, 1020)
# Wednesday:
#    9:00 to 9:30 -> (540, 570)
#    10:00 to 11:00 -> (600, 660)
#    12:30 to 15:30 -> (750, 930)
#    16:00 to 16:30 -> (960, 990)
joyce_busy = {
    0: [(540, 570), (600, 660), (690, 750), (780, 900), (930, 1020)],
    1: [(540, 1020)],  # Fully busy
    2: [(540, 570), (600, 660), (750, 930), (960, 990)]
}

# Joyce has a preference: she would rather not meet on Monday before 12:00.
# We enforce that if the meeting is on Monday (day 0), then the meeting must start at 12:00 (720 minutes) or later.
def apply_joyce_preference(day, solver):
    if day == 0:
        solver.add(start >= 720)

# Helper function:
# The meeting interval [start, start+duration) must NOT overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    # Either the meeting ends before busy interval starts,
    # or the meeting starts after the busy interval ends.
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None
meeting_start_val = None

# Iterate over candidate days (ordered) to satisfy the "earliest availability" request.
for day in candidate_days:
    solver = Solver()
    # Meeting must lie within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply Joyce's scheduling preference for Monday.
    apply_joyce_preference(day, solver)
    
    # Add Joshua's busy constraints for this day.
    for b_start, b_end in joshua_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add Joyce's busy constraints for this day.
    for b_start, b_end in joyce_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Iterate minute-by-minute to ensure we find the earliest available meeting time on this day.
    for t in range(WORK_START, WORK_END - duration + 1):
        # When day==0, ensure t satisfies Joyce’s preference (t >= 720)
        if day == 0 and t < 720:
            continue
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start_val = t
            meeting_day = day
            found = True
            solver.pop()
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end_val = meeting_start_val + duration
    start_hr, start_min = divmod(meeting_start_val, 60)
    end_hr, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")