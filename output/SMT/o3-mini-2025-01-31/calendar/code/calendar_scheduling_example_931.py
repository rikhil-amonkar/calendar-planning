from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # workday starts at 9:00 (minutes from midnight)
WORK_END = 17 * 60     # workday ends at 17:00

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Noah's busy intervals (in minutes from midnight):
# Monday: 9:00-10:00, 12:00-12:30, 13:00-13:30, 15:30-16:00
# Tuesday: 9:00-10:30, 11:00-11:30, 12:00-12:30, 14:00-15:00, 16:00-17:00
# Wednesday: 10:00-12:00, 14:00-15:00, 15:30-16:00, 16:30-17:00
# Thursday: 10:00-10:30, 11:00-12:00, 16:00-16:30
# Friday: 9:30-10:00, 10:30-12:00, 12:30-13:30, 15:00-15:30, 16:30-17:00
noah_busy = {
    0: [(9*60, 10*60), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (15*60 + 30, 16*60)],
    1: [(9*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (14*60, 15*60), (16*60, 17*60)],
    2: [(10*60, 12*60), (14*60, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)],
    3: [(10*60, 10*60 + 30), (11*60, 12*60), (16*60, 16*60 + 30)],
    4: [(9*60 + 30, 10*60), (10*60 + 30, 12*60), (12*60 + 30, 13*60 + 30), (15*60, 15*60 + 30), (16*60 + 30, 17*60)]
}

# Kathryn's busy intervals (in minutes from midnight):
# Monday: 9:00-12:00, 13:00-14:30, 15:00-17:00
# Tuesday: 9:00-12:30, 13:00-17:00
# Wednesday: 9:00-9:30, 12:30-17:00
# Thursday: 9:00-11:30, 12:00-13:00, 14:00-15:00, 15:30-17:00
# Friday: 9:00-11:00, 11:30-12:30, 13:00-16:00
kathryn_busy = {
    0: [(9*60, 12*60), (13*60, 14*60 + 30), (15*60, 17*60)],
    1: [(9*60, 12*60 + 30), (13*60, 17*60)],
    2: [(9*60, 9*60 + 30), (12*60 + 30, 17*60)],
    3: [(9*60, 11*60 + 30), (12*60, 13*60), (14*60, 15*60), (15*60 + 30, 17*60)],
    4: [(9*60, 11*60), (11*60 + 30, 12*60 + 30), (13*60, 16*60)]
}

# Preferences:
# Noah would like to avoid more meetings on Wednesday.
# Since this is a preference and not an absolute constraint,
# we try to schedule on other days first if possible.
# Thus, we set allowed days (hard constraint) to exclude Wednesday.
allowed_days_noah = {0, 1, 3, 4}
# Kathryn has no day preferences.
allowed_days_kathryn = {0, 1, 2, 3, 4}

# The meeting day must be in the intersection of allowed days.
allowed_days = sorted(list(allowed_days_noah.intersection(allowed_days_kathryn)))
# In this case, allowed_days = [0, 1, 3, 4] (Monday, Tuesday, Thursday, Friday)

# Helper function: ensure that a meeting [s, s+duration] does NOT overlap a busy interval [b_start, b_end].
def no_overlap(b_start, b_end, meeting_start, duration):
    return Or(meeting_start + duration <= b_start, meeting_start >= b_end)

def find_earliest_meeting():
    # Iterate allowed days in order: Monday, Tuesday, Thursday, Friday.
    for day in allowed_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # The meeting must be scheduled during work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add constraints for Noah's busy intervals on this day.
        if day in noah_busy:
            for (busy_start, busy_end) in noah_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Add constraints for Kathryn's busy intervals on this day.
        if day in kathryn_busy:
            for (busy_start, busy_end) in kathryn_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))

        # Try every possible start time within the work hours.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

# Run the search for earliest meeting time that meets all constraints.
day, start_time = find_earliest_meeting()

if day is not None and start_time is not None:
    meeting_end = start_time + duration
    sh, sm = divmod(start_time, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")