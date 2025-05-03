from z3 import Solver, Int, Or, sat

# Meeting duration: 30 minutes.
duration = 30

# Work day hours in minutes (from midnight): 9:00 is 540 and 17:00 is 1020.
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days represented as integers:
# Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
candidate_days = [0, 1, 2, 3]

# Busy schedules (intervals are in minutes from midnight)
# Douglas's schedule:
#   Wednesday: 12:30-13:00  => (750,780)
#   Thursday: 13:30-14:00   => (810,840)
douglas_busy = {
    2: [(750, 780)],  # Wednesday
    3: [(810, 840)]   # Thursday
}

# Zachary's schedule:
# Monday:
#   9:00-10:30  => (540,630)
#   11:00-12:30 => (660,750)
#   13:00-15:00 => (780,900)
#   15:30-17:00 => (930,1020)
#
# Tuesday:
#   9:00-10:30  => (540,630)
#   11:30-12:00 => (690,720)
#   12:30-13:00 => (750,780)
#   14:30-16:30 => (870,990)
#
# Wednesday:
#   10:00-10:30 => (600,630)
#   11:00-11:30 => (660,690)
#   13:30-14:00 => (810,840)
#   15:30-16:30 => (930,990)
#
# Thursday:
#   9:00-10:00   => (540,600)
#   10:30-11:00  => (630,660)
#   11:30-12:00  => (690,720)
#   13:00-13:30  => (780,810)
#   15:30-16:00  => (930,960)
#   16:30-17:00  => (990,1020)
zachary_busy = {
    0: [(540,630), (660,750), (780,900), (930,1020)],
    1: [(540,630), (690,720), (750,780), (870,990)],
    2: [(600,630), (660,690), (810,840), (930,990)],
    3: [(540,600), (630,660), (690,720), (780,810), (930,960), (990,1020)]
}

# Preference constraints:
# Douglas does not want to meet on Tuesday and Wednesday, and on Monday he doesn't want meetings after 13:30.
# Zachary would rather not meet on Thursday.
#
# We enforce these as hard constraints:
# - For Douglas: Allowed days are Monday (0) provided the meeting ends by 13:30 (i.e. start + duration <= 13:30 => 13*60+30 = 810)
#   or Thursday (3). (Tuesday (1) and Wednesday (2) are disallowed for him.)
# - For Zachary: Disallow Thursday (3).

solution_found = False
selected_day = None
selected_start = None

# Helper: ensure meeting at "start_var" (duration minutes) does not overlap busy intervals [busy_start, busy_end)
def no_overlap(busy_start, busy_end, start_var):
    return Or(start_var + duration <= busy_start, start_var >= busy_end)

# We iterate over candidate days (Monday, Tuesday, Wednesday, Thursday) in order.
for day in candidate_days:
    solver = Solver()
    start = Int("start")
    solver.add(start >= WORK_START, start + duration <= WORK_END)
    
    # Apply the preference constraints for Douglas:
    # Douglas avoids Tuesday (1) and Wednesday (2).
    if day == 1 or day == 2:
        solver.add(False)
    # On Monday, Douglas doesn't want meetings after 13:30, meaning the meeting must end by 13:30.
    if day == 0:
        solver.add(start + duration <= 13 * 60 + 30)  # meeting must finish by 13:30
    
    # Apply preference for Zachary: he would rather not meet on Thursday.
    if day == 3:
        solver.add(False)
    
    # Add busy interval constraints for Douglas on the day, if any.
    for (busy_start, busy_end) in douglas_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Add busy interval constraints for Zachary on the day.
    for (busy_start, busy_end) in zachary_busy.get(day, []):
        solver.add(no_overlap(busy_start, busy_end, start))
    
    # Search for an available meeting time by iterating minute-by-minute.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(start == t)
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
    # Convert minutes to HH:MM format.
    start_hour, start_min = divmod(selected_start, 60)
    end_hour, end_min = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")