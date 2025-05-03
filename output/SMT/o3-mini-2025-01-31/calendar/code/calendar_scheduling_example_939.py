from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # duration in minutes
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Busy intervals are represented as a tuple (start, end) in minutes.
# Donna's busy intervals:
# Monday: 12:00 to 12:30, 16:30 to 17:00
# Wednesday: 9:30 to 10:00
# Friday: 16:00 to 16:30
donna_busy = {
    0: [(12*60, 12*60+30), (16*60+30, 17*60)],
    2: [(9*60+30, 10*60)],
    4: [(16*60, 16*60+30)]
}

# Kenneth's busy intervals:
# Monday: 9:00 to 12:00, 13:00 to 13:30, 15:00 to 15:30, 16:00 to 17:00
# Tuesday: 9:00 to 13:30, 14:30 to 17:00
# Wednesday: 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:00 to 14:30, 15:00 to 16:30
# Thursday: 9:00 to 11:00, 11:30 to 13:30, 14:00 to 16:30
# Friday: 9:00 to 9:30, 10:00 to 17:00
kenneth_busy = {
    0: [(9*60, 12*60), (13*60, 13*60+30), (15*60, 15*60+30), (16*60, 17*60)],
    1: [(9*60, 13*60+30), (14*60+30, 17*60)],
    2: [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 14*60+30), (15*60, 16*60+30)],
    3: [(9*60, 11*60), (11*60+30, 13*60+30), (14*60, 16*60+30)],
    4: [(9*60, 9*60+30), (10*60, 17*60)]
}

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # The meeting must finish before the busy slot starts or start after it ends.
    # That is, (meeting_start + duration <= busy_start) OR (meeting_start >= busy_end).
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Iterate over days in order: Monday (0) to Friday (4)
    for day in range(5):
        solver = Solver()
        # s: meeting start time (in minutes from midnight on this day)
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Donna's busy intervals constraints for this day, if any.
        if day in donna_busy:
            for (busy_start, busy_end) in donna_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Kenneth's busy intervals constraints for this day, if any.
        if day in kenneth_busy:
            for (busy_start, busy_end) in kenneth_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Check minute-by-minute from earliest possible time to latest possible start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                # We return the day and meeting start time in minutes.
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