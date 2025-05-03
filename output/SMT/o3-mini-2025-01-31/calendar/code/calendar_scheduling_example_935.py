from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # 30 minutes meeting
WORK_START = 9 * 60   # 9:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Terry's busy intervals (in minutes from midnight)
# Monday: 10:30-11:00, 12:30-14:00, 15:00-17:00
# Tuesday: 9:30-10:00, 10:30-11:00, 14:00-14:30, 16:00-16:30
# Wednesday: 9:30-10:30, 11:00-12:00, 13:00-13:30, 15:00-16:00, 16:30-17:00
# Thursday: 9:30-10:00, 12:00-12:30, 13:00-14:30, 16:00-16:30
# Friday: 9:00-11:30, 12:00-12:30, 13:30-16:00, 16:30-17:00
terry_busy = {
    0: [(10*60+30, 11*60), (12*60+30, 14*60), (15*60, 17*60)],
    1: [(9*60+30, 10*60), (10*60+30, 11*60), (14*60, 14*60+30), (16*60, 16*60+30)],
    2: [(9*60+30, 10*60+30), (11*60, 12*60), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)],
    3: [(9*60+30, 10*60), (12*60, 12*60+30), (13*60, 14*60+30), (16*60, 16*60+30)],
    4: [(9*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 16*60), (16*60+30, 17*60)]
}

# Frances's busy intervals (in minutes from midnight)
# Monday: 9:30-11:00, 11:30-13:00, 14:00-14:30, 15:00-16:00
# Tuesday: 9:00-9:30, 10:00-10:30, 11:00-12:00, 13:00-14:30, 15:30-16:30
# Wednesday: 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
# Thursday: 11:00-12:30, 14:30-17:00
# Friday: 9:30-10:30, 11:00-12:30, 13:00-16:00, 16:30-17:00
frances_busy = {
    0: [(9*60+30, 11*60), (11*60+30, 13*60), (14*60, 14*60+30), (15*60, 16*60)],
    1: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (13*60, 14*60+30), (15*60+30, 16*60+30)],
    2: [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 16*60), (16*60+30, 17*60)],
    3: [(11*60, 12*60+30), (14*60+30, 17*60)],
    4: [(9*60+30, 10*60+30), (11*60, 12*60+30), (13*60, 16*60), (16*60+30, 17*60)]
}

# Helper function to ensure meeting interval [s, s+duration] does not overlap busy interval [busy_start, busy_end]
def no_overlap(busy_start, busy_end, meeting_start, duration):
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Because Frances prefers to avoid Tuesday, we try days in this order:
    # Monday (0), Wednesday (2), Thursday (3), Friday (4), and finally Tuesday (1) if needed.
    preferred_days = [0, 2, 3, 4, 1]
    
    for day in preferred_days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight

        # Meeting must be within work hours: [9:00, 17:00]
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Terry's constraints for the day if any busy slots exist
        if day in terry_busy:
            for (busy_start, busy_end) in terry_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Frances's constraints for the day if any busy slots exist
        if day in frances_busy:
            for (busy_start, busy_end) in frances_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Check every possible start minute in the work day for a valid meeting time
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
    start_hour, start_min = divmod(start_time, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time found that satisfies all constraints.")