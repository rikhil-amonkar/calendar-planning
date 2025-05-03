from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes
duration = 30
# Meeting start time variable (in minutes from midnight)
start = Int("start")

# Define work hours in minutes from midnight: 9:00 -> 17:00
WORK_START = 540   # 9 * 60
WORK_END = 1020    # 17 * 60

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Preferences:
# • Donna would rather not meet on Tuesday.
# • Cynthia does not want to meet on Monday.
# To satisfy both, we prefer Wednesday first.
# So our candidate days (in order of preference) become: Wednesday, Tuesday, then Monday.
candidate_days = [2, 1, 0]

# Busy schedules (times in minutes from midnight)

# Donna's busy schedule:
# Monday: 10:00-10:30, 11:00-11:30, 12:30-13:00, 16:00-17:00
# Tuesday: 9:00-9:30, 13:30-14:00, 14:30-16:00
# Wednesday: 11:00-11:30, 12:00-14:00, 16:00-16:30
donna_busy = {
    0: [(600, 630), (660, 690), (750, 780), (960, 1020)],
    1: [(540, 570), (810, 840), (870, 960)],
    2: [(660, 690), (720, 840), (960, 990)]
}

# Cynthia's busy schedule:
# Monday: 9:00-12:00, 12:30-17:00
# Tuesday: 9:00-9:30, 10:00-12:30, 14:00-14:30, 15:00-16:00
# Wednesday: 10:00-11:30, 12:00-12:30, 13:00-13:30, 16:00-16:30
cynthia_busy = {
    0: [(540, 720), (750, 1020)],
    1: [(540, 570), (600, 750), (840, 870), (900, 960)],
    2: [(600, 690), (720, 750), (780, 810), (960, 990)]
}

# Helper: A meeting scheduled at [start, start+duration) must not overlap a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # will hold the chosen day index (0, 1, or 2)
meeting_start_val = None # will hold the chosen start time in minutes from midnight

# Iterate over candidate days in the preferred order.
for day in candidate_days:
    solver = Solver()
    # The meeting must be within work hours.
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add Donna's busy time constraints for this day.
    for (busy_start, busy_end) in donna_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Add Cynthia's busy time constraints for this day.
    for (busy_start, busy_end) in cynthia_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # We want the earliest available time in the day, so iterate minute-by-minute.
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
    start_hour, start_min = divmod(meeting_start_val, 60)
    end_hour, end_min = divmod(meeting_end_val, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print(f"A valid meeting time is on {day_names[meeting_day]} from "
          f"{start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")