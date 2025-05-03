from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours in minutes: from 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540 minutes
WORK_END   = 17 * 60   # 1020 minutes

# Days are encoded as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
# Henry does not want to meet on Monday or Tuesday, so his allowed days are Wednesday and Thursday.
# Scott prefers to avoid meetings on Wednesday after 13:30.
# Hence, our candidate days become:
#   Wednesday (2) with the extra constraint: meeting must finish by 13:30 (i.e. s + duration <= 810)
#   Thursday (3)
candidate_days = [2, 3]

# Define busy intervals as a dictionary mapping day -> list of intervals [start, end)
# Times are in minutes from midnight.
# Note: We only include days that are candidates

# Scott's busy schedule:
# Wednesday: 14:30 to 15:00 -> (14*60+30, 15*60) = (870, 900)
# Thursday: 9:00 to 9:30 -> (540,570), 13:30 to 14:00 -> (810,840), 16:00 to 16:30 -> (960,990)
scott_busy = {
    2: [(870, 900)],
    3: [(540, 570), (810, 840), (960, 990)]
}

# Henry's busy schedule:
# Wednesday: 9:00 to 10:30 -> (540,630), 11:30 to 12:30 -> (690,750),
#            13:30 to 14:00 -> (810,840), 14:30 to 16:00 -> (870,960)
# Thursday: 10:00 to 11:00 -> (600,660)
henry_busy = {
    2: [(540, 630), (690, 750), (810, 840), (870, 960)],
    3: [(600, 660)]
}

# Function to ensure that a meeting starting at time s (lasting 'duration') does not overlap
# with a busy interval [b_start, b_end).
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Iterate through candidate days (Wednesday first, then Thursday)
for day in candidate_days:
    solver = Solver()
    s = Int("s")  # Meeting start time in minutes.
    
    # The meeting must fit within work hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)
    
    # For Wednesday, add Scott's preference: avoid meetings after 13:30.
    # To ensure the meeting finishes by 13:30 (810 minutes):
    if day == 2:
        solver.add(s + duration <= 810)
    
    # Add Scott's busy intervals constraints.
    for (b_start, b_end) in scott_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Add Henry's busy intervals constraints.
    for (b_start, b_end) in henry_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))
    
    # Search for the earliest possible meeting start time.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()
            break
        solver.pop()
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM format
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")