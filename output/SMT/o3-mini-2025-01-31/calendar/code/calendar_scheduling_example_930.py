from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (half an hour)
WORK_START = 9 * 60    # work day begins at 9:00 (540 minutes)
WORK_END = 17 * 60     # work day ends at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Jean's busy intervals (times in minutes from midnight)
# Monday: 10:00-10:30, 12:00-12:30, 13:30-14:00, 15:00-15:30, 16:30-17:00
# Tuesday: 10:00-10:30, 14:00-14:30, 16:00-16:30
# Thursday: 14:00-14:30, 15:00-15:30
# Friday: 9:30-10:00, 11:00-11:30, 12:00-12:30, 14:30-15:00
jean_busy = {
    0: [(10*60, 10*60 + 30), (12*60, 12*60 + 30), (13*60 + 30, 14*60), (15*60, 15*60 + 30), (16*60 + 30, 17*60)],
    1: [(10*60, 10*60 + 30), (14*60, 14*60 + 30), (16*60, 16*60 + 30)],
    3: [(14*60, 14*60 + 30), (15*60, 15*60 + 30)],
    4: [(9*60 + 30, 10*60), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (14*60 + 30, 15*60)]
}

# Jennifer's busy intervals (times in minutes from midnight)
# Monday: 10:30-11:00, 12:00-12:30, 14:30-15:00, 16:00-17:00
# Tuesday: 10:00-13:30, 14:30-15:00
# Wednesday: 9:00-11:30, 12:00-13:30, 14:30-17:00
# Thursday: 9:30-10:00, 12:00-13:00, 13:30-14:00, 14:30-15:00, 16:30-17:00
# Friday: 10:00-11:00, 12:00-13:30, 14:30-17:00
jennifer_busy = {
    0: [(10*60 + 30, 11*60), (12*60, 12*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)],
    1: [(10*60, 13*60 + 30), (14*60 + 30, 15*60)],
    2: [(9*60, 11*60 + 30), (12*60, 13*60 + 30), (14*60 + 30, 17*60)],
    3: [(9*60 + 30, 10*60), (12*60, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 15*60), (16*60 + 30, 17*60)],
    4: [(10*60, 11*60), (12*60, 13*60 + 30), (14*60 + 30, 17*60)]
}

# Participant preferences:
# Jean would rather not meet on Monday.
# Jean would rather not have a meeting on Thursday starting at or after 10:00.
# Jennifer would like to avoid meetings on Tuesday, Wednesday, and Friday.
allowed_days_jean = {1, 2, 3, 4}       # Excluding Monday (day 0)
allowed_days_jennifer = {0, 3}           # Only Monday and Thursday allowed for Jennifer
# Intersection gives the days that satisfy both participants' preferences.
allowed_days = sorted(list(allowed_days_jean.intersection(allowed_days_jennifer)))
# This results in allowed_days = [3] (i.e., only Thursday)

# Helper function: ensures meeting [s, s+duration] doesn't overlap a busy interval [b_start, b_end].
def no_overlap(b_start, b_end, meeting_start, duration):
    return Or(meeting_start + duration <= b_start, meeting_start >= b_end)

def find_earliest_meeting():
    for day in allowed_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # If the day is Thursday (day 3), Jean prefers a meeting that starts before 10:00.
        if day == 3:
            solver.add(s < 10 * 60)
            
        # Add Jean's busy time constraints.
        if day in jean_busy:
            for (busy_start, busy_end) in jean_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Jennifer's busy time constraints.
        if day in jennifer_busy:
            for (busy_start, busy_end) in jennifer_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Try each potential start time from WORK_START up to the latest start.
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
    sh, sm = divmod(start_time, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[day], sh, sm, eh, em))
else:
    print("No valid meeting time found that satisfies all constraints.")