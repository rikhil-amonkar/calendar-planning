from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration is 30 minutes
WORK_START = 9 * 60    # Work hours start at 9:00 (540 minutes)
WORK_END = 17 * 60     # Work hours end at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Thomas's busy intervals per day (in minutes from midnight)
thomas_busy = {
    0: [(13 * 60, 14 * 60), (16 * 60 + 30, 17 * 60)],           # Monday: 13:00-14:00, 16:30-17:00
    1: [(14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],         # Tuesday: 14:00-14:30, 16:30-17:00
    2: [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)], # Wednesday
    3: [(10 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
        (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],          # Thursday
    4: [(10 * 60 + 30, 11 * 60), (12 * 60 + 30, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)]  # Friday
}

# Jennifer's busy intervals per day (in minutes from midnight)
jennifer_busy = {
    0: [(9 * 60, 17 * 60)],   # Monday: busy all day 9:00-17:00
    1: [(9 * 60, 17 * 60)],   # Tuesday: busy all day 9:00-17:00
    2: [(9 * 60, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],  # Wednesday
    3: [(9 * 60, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (15 * 60, 16 * 60 + 30)], # Thursday
    4: [(9 * 60, 12 * 60), (12 * 60 + 30, 17 * 60)]   # Friday
}

# Helper function for non-overlap constraint:
def no_overlap(b_start, b_end, s, duration):
    # The meeting [s, s+duration] must either end before the busy interval starts
    # or start after the busy interval ends.
    return Or(s + duration <= b_start, s >= b_end)

def find_earliest_meeting():
    # We'll check days in order Monday to Friday.
    # Note: On Monday and Tuesday, Jennifer is busy all day,
    # so the actual available days will likely be Wednesday, Thursday, or Friday.
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight for the given day

        # Constraint: the meeting must be within work hours
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Thomas's busy intervals constraints for the day (if present)
        if day in thomas_busy:
            for (b_start, b_end) in thomas_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Add Jennifer's busy intervals constraints for the day (if present)
        if day in jennifer_busy:
            for (b_start, b_end) in jennifer_busy[day]:
                solver.add(no_overlap(b_start, b_end, s, duration))

        # Try every possible start minute from WORK_START to latest valid starting minute
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    start_hr, start_min = divmod(start_time, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")