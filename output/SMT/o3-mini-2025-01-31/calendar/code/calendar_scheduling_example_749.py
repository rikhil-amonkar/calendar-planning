from z3 import Solver, Int, Or, sat

# Duration of the meeting in minutes (30 minutes)
duration = 30

# Meeting start time variable (in minutes after midnight)
start = Int("start")

# Work hours in minutes: from 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 540
WORK_END = 1020

# Days encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# According to the constraints:
#   - Anthony cannot meet on Monday.
#   - Anthony cannot meet on Wednesday.
#   - On Tuesday, Anthony does not want meetings after 14:00.
# Therefore, the only candidate day is Tuesday.
candidate_days = [1]

# Scott has no meetings all week, so no busy intervals for him.

# Anthony's busy schedule (times in minutes after midnight):
# Monday: 9:30-13:00, 13:30-14:30, 15:00-16:30
# Tuesday: 9:00-11:00, 11:30-14:00, 14:30-17:00
# Wednesday: 9:00-11:00, 11:30-12:00, 12:30-13:00, 14:30-16:30
# (We only consider Tuesday since Anthony cannot meet on Monday or Wednesday.)
anthony_busy = {
    1: [(540, 660),   # 9:00 to 11:00
        (690, 840),   # 11:30 to 14:00
        (870, 1020)]  # 14:30 to 17:00 (this does not matter because of the 'no meeting after 14:00' preference)
}

# Anthony also prefers not to have meetings after 14:00 on Tuesday.
TUESDAY_MEETING_DEADLINE = 840  # 14:00 in minutes

# Helper function: For a meeting that spans [start, start+duration),
# it should NOT overlap with a busy interval [busy_start, busy_end).
def non_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

found = False
meeting_day = None       # Selected day (will be 1 for Tuesday)
meeting_start_val = None # Selected meeting start time (in minutes from midnight)

# Iterate over candidate days (only Tuesday in this case)
for day in candidate_days:
    solver = Solver()
    # Constrain meeting to be within work hours
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Since Tuesday meetings should not be scheduled after 14:00,
    # ensure the meeting finishes by 14:00.
    if day == 1:
        solver.add(start + duration <= TUESDAY_MEETING_DEADLINE)
    
    # Add Anthony's busy constraints for Tuesday
    for busy_start, busy_end in anthony_busy.get(day, []):
        solver.add(non_overlap(busy_start, busy_end))
    
    # Scott has no busy intervals
    
    # Check each minute in the possible time window to find the earliest valid meeting time.
    # Because of Anthony's busy schedule on Tuesday, the only available gap before 14:00 is between
    # 11:00 and 11:30: meeting from 660 to 690.
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
    print(f"A valid meeting time is on {day_names[meeting_day]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}.")
else:
    print("No valid meeting time could be found that meets all constraints.")