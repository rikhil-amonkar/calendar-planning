from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30                  # meeting duration in minutes
WORK_START = 9 * 60            # work day starts at 9:00 (540 minutes)
WORK_END = 17 * 60             # work day ends at 17:00 (1020 minutes)

# Day mapping: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Participant busy intervals (in minutes):

# George's busy intervals:
# Tuesday: 13:00 to 14:30 and 16:00 to 16:30  -> [(780, 870), (960, 990)]
# Wednesday: 14:00 to 14:30 and 15:30 to 17:00   -> [(840, 870), (930, 1020)]
# Thursday: 10:30 to 11:00, 12:30 to 13:00, 14:30 to 15:00, 16:30 to 17:00
#           -> [(630, 660), (750, 780), (870, 900), (990, 1020)]
# Friday: 9:30 to 10:00, 14:30 to 15:00            -> [(570, 600), (870, 900)]
george_busy = {
    1: [(13 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    2: [(14 * 60, 14 * 60 + 30), (15 * 60 + 30, 17 * 60)],
    3: [(10 * 60 + 30, 11 * 60), (12 * 60 + 30, 13 * 60),
        (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
    4: [(9 * 60 + 30, 10 * 60), (14 * 60 + 30, 15 * 60)]
}

# Evelyn's busy intervals:
# Monday:    10:00-11:00, 12:30-13:00, 13:30-14:00, 14:30-15:30, 16:00-17:00
#            -> [(600,660), (750,780), (810,840), (870,930), (960,1020)]
# Tuesday:   9:00-9:30, 10:00-10:30, 11:00-13:00, 13:30-15:30, 16:00-16:30
#            -> [(540,570), (600,630), (660,780), (810,930), (960,990)]
# Wednesday: 9:00-12:00, 12:30-15:30, 16:30-17:00
#            -> [(540,720), (750,930), (990,1020)] but note that 9:00-12:00 means busy until 720.
# Thursday:  9:00-9:30, 10:30-11:30, 12:00-13:00, 13:30-17:00
#            -> [(540,570), (630,690), (720,780), (810,1020)]
# Friday:    9:00-9:30, 10:00-11:00, 12:00-13:00, 13:30-15:00, 16:00-17:00
#            -> [(540,570), (600,660), (720,780), (810,900), (960,1020)]
evelyn_busy = {
    0: [(10 * 60, 11 * 60), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 13 * 60), (13 * 60 + 30, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    2: [(9 * 60, 12 * 60), (12 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 13 * 60), (13 * 60 + 30, 17 * 60)],
    4: [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60, 13 * 60), (13 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
}

# Avoid constraints:
# George cannot meet on Monday (day 0)
# Evelyn would like to avoid more meetings on Tuesday (day 1) and Wednesday (day 2)
george_avoid = {0}
evelyn_avoid = {1, 2}

def no_overlap(busy_start, busy_end, s, dur):
    # Meeting [s, s+dur) does not overlap with busy interval [busy_start, busy_end)
    return Or(s + dur <= busy_start, s >= busy_end)

def find_earliest_meeting():
    # Search days in order: Monday (0) to Friday (4)
    for day in range(5):
        # Skip days if any participant's avoid constraint applies
        if day in george_avoid or day in evelyn_avoid:
            continue

        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Ensure meeting is within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add George's constraints for the day.
        if day in george_busy:
            for busy_start, busy_end in george_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add Evelyn's constraints for the day.
        if day in evelyn_busy:
            for busy_start, busy_end in evelyn_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Check each minute from work start to work_end - duration.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                model = solver.model()
                return day, model[s].as_long()
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    sh, sm = divmod(start_time, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")