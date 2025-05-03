from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60  # one hour meeting in minutes
WORK_START = 9 * 60    # work day starts at 9:00 (in minutes)
WORK_END = 17 * 60     # work day ends at 17:00 (in minutes)

# Day encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Anthony's busy intervals (in minutes from midnight)
# Monday: 10:30-11:00, 13:00-14:00, 16:30-17:00
# Tuesday: 9:30-11:00, 11:30-12:00, 13:30-14:00, 15:30-16:00
# Wednesday: 10:00-11:00, 13:00-13:30, 14:00-14:30, 16:30-17:00
# Thursday: 10:30-11:00, 11:30-12:30, 13:30-14:30, 15:00-16:00, 16:30-17:00
# Friday: 9:00-11:00, 11:30-15:30, 16:30-17:00
anthony_busy = {
    0: [(9*60+30, 11*60), (13*60, 14*60), (16*60+30, 17*60)],
    1: [(9*60+30, 11*60), (11*60+30, 12*60), (13*60+30, 14*60), (15*60+30, 16*60)],
    2: [(10*60, 11*60), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)],
    3: [(10*60+30, 11*60), (11*60+30, 12*60+30), (13*60+30, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)],
    4: [(9*60, 11*60), (11*60+30, 15*60+30), (16*60+30, 17*60)]
}

# Randy's busy intervals (in minutes from midnight)
# Monday: 9:00-17:00 (completely busy)
# Tuesday: 9:00-9:30, 10:00-12:30, 13:00-17:00
# Wednesday: 9:00-11:30, 12:00-12:30, 13:00-16:30
# Thursday: 10:00-11:30, 12:30-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
# Friday: 9:00-17:00 (completely busy)
randy_busy = {
    0: [(9*60, 17*60)],
    1: [(9*60, 9*60+30), (10*60, 12*60+30), (13*60, 17*60)],
    2: [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 16*60+30)],
    3: [(10*60, 11*60+30), (12*60+30, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)],
    4: [(9*60, 17*60)]
}

# Helper function: meeting [s, s+duration] should not overlap busy interval [busy_start, busy_end]
def no_overlap(busy_start, busy_end, meeting_start, duration):
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # We'll check each day from Monday to Friday
    for day in range(5):
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Ensure meeting time is within work hours: [9:00, 17:00]
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Anthony's busy intervals for the day:
        if day in anthony_busy:
            for (busy_start, busy_end) in anthony_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add constraints for Randy's busy intervals for the day:
        if day in randy_busy:
            for (busy_start, busy_end) in randy_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Iterate over each possible start time (minute granularity)
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