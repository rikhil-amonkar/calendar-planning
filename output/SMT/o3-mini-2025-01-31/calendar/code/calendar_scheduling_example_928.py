from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # meeting duration is 1 hour (60 minutes)
WORK_START = 9 * 60    # work day begins at 9:00 (540 minutes)
WORK_END = 17 * 60     # work day ends at 17:00 (1020 minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Joseph's busy intervals per day (times in minutes from midnight)
joseph_busy = {
    0: [(10*60 + 30, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60), (15*60 + 30, 16*60 + 30)],  # Monday
    1: [(15*60, 16*60)],                                                                           # Tuesday
    2: [(13*60 + 30, 14*60), (16*60, 16*60 + 30)],                                                 # Wednesday
    3: [(13*60, 13*60 + 30), (14*60, 14*60 + 30), (16*60 + 30, 17*60)],                            # Thursday
    4: [(10*60, 10*60 + 30), (13*60 + 30, 14*60)]                                                  # Friday
}

# Austin's busy intervals per day (times in minutes from midnight)
austin_busy = {
    0: [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (13*60, 13*60 + 30), (15*60, 17*60)],            # Monday
    1: [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 12*60), (13*60, 13*60 + 30), (14*60, 17*60)],# Tuesday
    2: [(9*60, 11*60), (12*60, 13*60), (13*60 + 30, 17*60)],                                       # Wednesday
    3: [(9*60, 17*60)],                                                                           # Thursday (busy all day)
    4: [(9*60 + 30, 10*60), (10*60 + 30, 11*60), (12*60, 13*60), (13*60 + 30, 14*60), (15*60, 17*60)] # Friday
}

# Helper function to specify that the meeting does not overlap a busy interval.
def no_overlap(b_start, b_end, meeting_start, duration):
    # The meeting [meeting_start, meeting_start + duration] must either end 
    # before the busy interval starts or start after it ends.
    return Or(meeting_start + duration <= b_start, meeting_start >= b_end)

def find_earliest_meeting():
    # Try each day from Monday (0) to Friday (4)
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight for the given day

        # Meeting must lie within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add constraints for Joseph's busy intervals on this day, if any.
        if day in joseph_busy:
            for (busy_start, busy_end) in joseph_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add constraints for Austin's busy intervals on this day, if any.
        if day in austin_busy:
            for (busy_start, busy_end) in austin_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Try every possible starting minute in the work day.
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