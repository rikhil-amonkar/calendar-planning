from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (60 minutes)
duration = 60

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Bruce would like to avoid Monday, hence we only consider Tuesday and Wednesday.
candidate_days = [1, 2]

# Robert's busy schedule (times in minutes after midnight):
# Monday: 10:00 to 11:00          => (600, 660)
#         11:30 to 12:00          => (690, 720)
#         14:30 to 16:00          => (870, 960)
# Tuesday: 9:00 to 9:30           => (540, 570)
#          10:00 to 13:00         => (600, 780)
#          13:30 to 14:30         => (810, 870)
#          15:00 to 16:00         => (900, 960)
#          16:30 to 17:00         => (990, 1020)
# Wednesday: 10:30 to 11:00       => (630, 660)
#            12:00 to 12:30       => (720, 750)
#            13:30 to 14:00       => (810, 840)
#            15:00 to 15:30       => (900, 930)
robert_busy = {
    0: [(600, 660), (690, 720), (870, 960)],
    1: [(540, 570), (600, 780), (810, 870), (900, 960), (990, 1020)],
    2: [(630, 660), (720, 750), (810, 840), (900, 930)]
}

# Bruce's busy schedule (times in minutes after midnight):
# Monday: 11:00 to 11:30          => (660, 690)
#         12:00 to 12:30          => (720, 750)
#         13:00 to 14:00          => (780, 840)
#         14:30 to 15:30          => (870, 930)
#         16:00 to 16:30          => (960, 990)
# Tuesday: 9:00 to 10:30          => (540, 630)
#          11:00 to 12:30         => (660, 750)
#          13:00 to 14:00         => (780, 840)
#          14:30 to 15:00         => (870, 900)
#          16:00 to 17:00         => (960, 1020)
# Wednesday: 9:00 to 10:30        => (540, 630)
#            12:00 to 12:30       => (720, 750)
#            13:00 to 13:30       => (780, 810)
#            15:00 to 16:00       => (900, 960)
#            16:30 to 17:00       => (990, 1020)
bruce_busy = {
    0: [(660, 690), (720, 750), (780, 840), (870, 930), (960, 990)],
    1: [(540, 630), (660, 750), (780, 840), (870, 900), (960, 1020)],
    2: [(540, 630), (720, 750), (780, 810), (900, 960), (990, 1020)]
}

# Bruce would like to avoid meetings on Monday (already excluded)
# and avoid meetings on Wednesday after 14:00. On Wednesday, if scheduled,
# the meeting should finish by 14:00, i.e., start + duration <= 14:00 (840 minutes).

# Helper function: the interval [start, start+duration) must not overlap a busy interval [busy_start, busy_end)
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Selected day (1 for Tuesday, 2 for Wednesday)
meeting_start_val = None # Meeting start time (in minutes after midnight)

# Iterate over candidate days in order, finding the earliest available meeting time.
for day in candidate_days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Bruce's additional preference for Wednesday: meeting must finish by 14:00 (840 minutes)
    if day == 2:
        solver.add(start + duration <= 840)
    
    # Add Robert's busy constraints for the current day
    for busy_start, busy_end in robert_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Bruce's busy constraints for the current day
    for busy_start, busy_end in bruce_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Search for the earliest possible start time minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
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
    sh, sm = divmod(meeting_start_val, 60)
    eh, em = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")