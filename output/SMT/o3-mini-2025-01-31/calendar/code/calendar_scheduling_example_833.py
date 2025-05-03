from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Encode days as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Based on constraints:
#   - Frances does not want to meet on Monday after 15:00 (i.e. meeting must finish by 15:00 on Monday)
#   - Hannah cannot meet on Thursday.
# Also note that Hannah is busy all day on Wednesday.
# Therefore, the only viable candidate days are Monday and Tuesday.
candidate_days = [0, 1]  # 0: Monday, 1: Tuesday

# Busy intervals for each participant (times in minutes since midnight, intervals as [start, end))
# Frances's busy schedule:
# Monday: 11:30-12:00 -> (690,720), 13:00-13:30 -> (780,810), 14:30-15:00 -> (870,900)
# Tuesday: 9:30-10:00 -> (570,600), 10:30-11:00 -> (630,660), 12:30-14:30 -> (750,870), 15:00-17:00 -> (900,1020)
# Wednesday: 10:30-11:30 -> (630,690), 13:00-14:00 -> (780,840), 14:30-15:00 -> (870,900), 15:30-16:30 -> (930,990)
# Thursday: 9:00-10:00 -> (540,600), 12:30-13:00 -> (750,780), 13:30-14:00 -> (810,840)
frances_busy = {
    0: [(690,720), (780,810), (870,900)],
    1: [(570,600), (630,660), (750,870), (900,1020)],
    2: [(630,690), (780,840), (870,900), (930,990)],
    3: [(540,600), (750,780), (810,840)]
}

# Hannah's busy schedule:
# Monday: 9:30-10:00 -> (570,600), 10:30-11:30 -> (630,690), 12:00-13:00 -> (720,780), 14:00-16:00 -> (840,960), 16:30-17:00 -> (990,1020)
# Tuesday: 9:30-10:00 -> (570,600), 10:30-11:00 -> (630,660), 12:00-12:30 -> (720,750), 13:00-13:30 -> (780,810), 14:30-16:00 -> (870,960)
# Wednesday: 9:00-17:00 -> (540,1020)
# Thursday: 9:00-10:00 -> (540,600), 10:30-17:00 -> (630,1020)
hannah_busy = {
    0: [(570,600), (630,690), (720,780), (840,960), (990,1020)],
    1: [(570,600), (630,660), (720,750), (780,810), (870,960)],
    2: [(540,1020)],
    3: [(540,600), (630,1020)]
}

# Function to create a constraint stating that a meeting starting at time s (lasting duration minutes)
# does not overlap with a busy interval [b_start, b_end)
def no_overlap(b_start, b_end, s):
    return Or(s + duration <= b_start, s >= b_end)

solution_found = False
selected_day = None
selected_start = None

# Try candidate days in the chosen order.
for day in candidate_days:
    # Apply additional day-specific preferences:
    # - For Monday (day 0): Frances does not want to meet after 15:00.
    #   Hence, if meeting is scheduled on Monday, it must finish by 15:00 (15:00 is 900 minutes).
    solver = Solver()
    s = Int("s")  # meeting start time in minutes

    # The meeting must fit completely within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    if day == 0:
        # Meeting must finish by 15:00 on Monday.
        solver.add(s + duration <= 15 * 60)  # 15:00 is 900 minutes

    # Add constraints for Frances's busy intervals on this day.
    for (b_start, b_end) in frances_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))

    # Add constraints for Hannah's busy intervals on this day.
    for (b_start, b_end) in hannah_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))

    # Try to find an earliest valid meeting start time in minute increments.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove the last push before exiting the loop.
            break
        solver.pop()
    if solution_found:
        break

if solution_found:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")