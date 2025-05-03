from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # workday begins at 9:00 (540 minutes)
WORK_END = 17 * 60     # workday ends at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Kathleen's busy intervals (in minutes from midnight)
# Monday: 9:30 to 10:00, 14:00 to 14:30
# Tuesday: 9:00 to 9:30, 11:00 to 11:30, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:00
# Wednesday: 9:30 to 10:00, 13:00 to 13:30, 16:00 to 16:30
# Thursday: 9:00 to 9:30, 11:00 to 11:30, 13:00 to 13:30, 14:00 to 14:30
# Friday: 9:00 to 9:30, 14:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00
kathleen_busy = {
    0: [(9*60 + 30, 10*60), (14*60, 14*60 + 30)],
    1: [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60 + 30, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 15*60)],
    2: [(9*60 + 30, 10*60), (13*60, 13*60 + 30), (16*60, 16*60 + 30)],
    3: [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (13*60, 13*60 + 30), (14*60, 14*60 + 30)],
    4: [(9*60, 9*60 + 30), (14*60, 14*60 + 30), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
}

# Christian's busy intervals (in minutes from midnight)
# Monday: 9:00 to 12:00, 13:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00
# Tuesday: 9:00 to 9:30, 10:00 to 13:00, 13:30 to 14:00, 14:30 to 15:00, 15:30 to 17:00
# Wednesday: 9:30 to 17:00
# Thursday: 9:00 to 9:30, 11:00 to 13:00, 14:00 to 15:00, 15:30 to 17:00
# Friday: 9:30 to 11:30, 12:00 to 12:30, 13:00 to 14:00, 14:30 to 17:00
christian_busy = {
    0: [(9*60, 12*60), (13*60, 14*60 + 30), (15*60 + 30, 16*60), (16*60 + 30, 17*60)],
    1: [(9*60, 9*60 + 30), (10*60, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 17*60)],
    2: [(9*60 + 30, 17*60)],
    3: [(9*60, 9*60 + 30), (11*60, 13*60), (14*60, 15*60), (15*60 + 30, 17*60)],
    4: [(9*60 + 30, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 14*60), (14*60 + 30, 17*60)]
}

# Participant day preferences:
# Kathleen does not want to meet on Tuesday.
# Christian cannot meet on Monday, Wednesday, or Friday.
allowed_days_kathleen = {0, 2, 3, 4}  # Monday, Wednesday, Thursday, Friday
allowed_days_christian = {1, 3}         # Tuesday and Thursday

# The meeting day must be in the intersection.
allowed_days = sorted(list(allowed_days_kathleen.intersection(allowed_days_christian)))
# In this case, allowed_days will be [3] (i.e., Thursday)

# Helper function to ensure that meeting [s, s+duration] does not overlap a busy interval.
def no_overlap(b_start, b_end, meeting_start, duration):
    return Or(meeting_start + duration <= b_start, meeting_start >= b_end)

def find_earliest_meeting():
    # Loop over allowed days in ascending order.
    for day in allowed_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must be scheduled within the work day.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Kathleen's busy constraints for this day, if any.
        if day in kathleen_busy:
            for (busy_start, busy_end) in kathleen_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Christian's busy constraints for this day, if any.
        if day in christian_busy:
            for (busy_start, busy_end) in christian_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Check each minute from WORK_START up to the latest possible start time.
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
    print("No valid meeting time found that satisfies all constraints.")