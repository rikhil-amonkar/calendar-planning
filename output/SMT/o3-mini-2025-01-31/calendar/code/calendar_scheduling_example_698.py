from z3 import Solver, Int, Or, sat

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes from midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Busy schedules for each participant on Monday (day 0) and Tuesday (day 1)

# Ashley's busy schedule in minutes:
# Monday:
#   9:00 to 10:30 -> (540,630)
#   12:00 to 12:30 -> (720,750)
#   13:30 to 15:00 -> (810,900)
# Tuesday:
#   13:30 to 14:00 -> (810,840)
ashley_busy = {
    0: [(540,630), (720,750), (810,900)],
    1: [(810,840)]
}

# Kenneth's busy schedule in minutes:
# Monday:
#   9:30 to 10:30 -> (570,630)
#   11:00 to 11:30 -> (660,690)
#   13:30 to 14:00 -> (810,840)
#   14:30 to 16:00 -> (870,960)
#   16:30 to 17:00 -> (990,1020)
# Tuesday:
#   9:30 to 11:00  -> (570,660)
#   11:30 to 12:30 -> (690,750)
#   13:00 to 13:30 -> (780,810)
#   14:00 to 15:00 -> (840,900)
#   16:00 to 17:00 -> (960,1020)
kenneth_busy = {
    0: [(570,630), (660,690), (810,840), (870,960), (990,1020)],
    1: [(570,660), (690,750), (780,810), (840,900), (960,1020)]
}

# Note: Ashley would rather not meet on Tuesday. We handle this as a soft preference.
# For the purpose of this problem, we will first try to find an available time slot on Monday.
# Only if no valid slot is available on Monday, we will then consider Tuesday.

# Helper function: meeting interval [start, start+duration) must not overlap with busy interval [b_start, b_end)
def non_overlap(b_start, b_end):
    # Either the meeting ends before busy starts, or starts after busy ends.
    return Or(start + duration <= b_start, start >= b_end)

found = False
meeting_day = None  # 0 for Monday, 1 for Tuesday
meeting_start = None

# Try days in order: Monday (day=0) then Tuesday (day=1)
for day in [0, 1]:
    solver = Solver()
    
    # The meeting must be within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Add busy constraints for Ashley
    for b_start, b_end in ashley_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Add busy constraints for Kenneth
    for b_start, b_end in kenneth_busy.get(day, []):
        solver.add(non_overlap(b_start, b_end))
    
    # Loop through possible start times (in ascending order) to get the earliest availability
    start_time_min = WORK_START
    start_time_max = WORK_END - duration
    
    for t in range(start_time_min, start_time_max + 1):
        solver.push()
        solver.add(start == t)
        if solver.check() == sat:
            meeting_start = t
            meeting_day = day
            found = True
            solver.pop()  # remove the temporary constraint for t
            break
        solver.pop()
    
    if found:
        break

if found:
    meeting_end = meeting_start + duration
    # Convert minutes to HH:MM
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    day_str = "Monday" if meeting_day == 0 else "Tuesday"
    print(f"A valid meeting time is on {day_str} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")