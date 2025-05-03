from z3 import Solver, Int, Or, sat

# Meeting duration in minutes (60 minutes)
duration = 60

# Work hours in minutes: 9:00 (540) to 17:00 (1020)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Encode days as: Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
# Note Jose would rather not meet on Wednesday, so we skip that day.
# Judith would rather not meet on Monday before 15:00.
# We’ll try candidate days in our search order: first Thursday, then Monday, then Tuesday.
candidate_days = [3, 0, 1]

# Busy intervals for each participant (times in minutes since midnight, intervals are [start, end)).
# Jose's busy schedule:
# Monday: 14:30 to 15:00 -> (870,900)
# Tuesday: 10:30 to 11:00 -> (630,660)
# (No busy intervals given explicitly for Wednesday for Jose, but he prefers to avoid it.)
# Thursday: 9:00 to 9:30 -> (540,570), 13:30 to 14:00 -> (810,840)
jose_busy = {
    0: [(870,900)],
    1: [(630,660)],
    3: [(540,570), (810,840)]
}

# Judith's busy schedule:
# Monday: 9:30 to 10:00 -> (570,600), 13:00 to 13:30 -> (780,810), 16:00 to 16:30 -> (960,990)
# Tuesday: 9:00 to 9:30 -> (540,570), 10:00 to 15:30 -> (600,930), 16:00 to 17:00 -> (960,1020)
# Wednesday: 9:00 to 11:30 -> (540,690), 12:00 to 13:00 -> (720,780), 13:30 to 14:00 -> (810,840), 15:30 to 17:00 -> (930,1020)
# Thursday: 9:00 to 11:30 -> (540,690), 12:00 to 13:30 -> (720,810), 15:00 to 17:00 -> (900,1020)
judith_busy = {
    0: [(570,600), (780,810), (960,990)],
    1: [(540,570), (600,930), (960,1020)],
    2: [(540,690), (720,780), (810,840), (930,1020)],
    3: [(540,690), (720,810), (900,1020)]
}

solution_found = False
selected_day = None
selected_start = None

# Helper function to generate a non-overlap constraint.
# Meeting starting at s (of duration minutes) must not overlap a busy interval [b_start, b_end).
def no_overlap(b_start, b_end, s):
    # Either the meeting ends at or before b_start, or starts at or after b_end.
    return Or(s + duration <= b_start, s >= b_end)

# Iterate candidate days in the chosen order.
for day in candidate_days:
    # Exclude Wednesday (day 2) explicitly if it appears.
    if day == 2:
        continue

    solver = Solver()
    s = Int("s")  # meeting start time in minutes

    # The meeting must fit completely within working hours.
    solver.add(s >= WORK_START, s + duration <= WORK_END)

    # Add Judith's preference: If meeting is on Monday (day 0), avoid meeting before 15:00.
    if day == 0:
        solver.add(s >= 15 * 60)  # 15:00 is 900 minutes

    # Add constraints for busy intervals for Jose on this day.
    for (b_start, b_end) in jose_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))

    # Add constraints for busy intervals for Judith on this day.
    for (b_start, b_end) in judith_busy.get(day, []):
        solver.add(no_overlap(b_start, b_end, s))

    # Sometimes additional constraints arise from busy intervals that force the meeting 
    # into a specific window. For instance on Thursday, Judith's busy interval (900,1020)
    # means that the meeting must finish by 900 if scheduled before that busy block.
    # We can let the solver figure that out.

    # Find an earliest valid start time by trying all possible minute slots.
    for t in range(WORK_START, WORK_END - duration + 1):
        solver.push()
        solver.add(s == t)
        if solver.check() == sat:
            selected_start = t
            selected_day = day
            solution_found = True
            solver.pop()  # Remove last push before breaking
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