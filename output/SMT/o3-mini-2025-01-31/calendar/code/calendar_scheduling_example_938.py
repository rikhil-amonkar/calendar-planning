from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30  # duration in minutes
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Day encoding: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Eugene's busy intervals (times in minutes)
# Monday: 11:00-12:00, 13:30-14:00, 14:30-15:00, 16:00-16:30
# Wednesday: 9:00-9:30, 11:00-11:30, 12:00-12:30, 13:30-15:00
# Thursday: 9:30-10:00, 11:00-12:30
# Friday: 10:30-11:00, 12:00-12:30, 13:00-13:30
eugene_busy = {
    0: [(11*60, 12*60), (13*60+30, 14*60), (14*60+30, 15*60), (16*60, 16*60+30)],
    2: [(9*60, 9*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 15*60)],
    3: [(9*60+30, 10*60), (11*60, 12*60+30)],
    4: [(10*60+30, 11*60), (12*60, 12*60+30), (13*60, 13*60+30)]
}

# Eric's busy intervals (times in minutes)
# Monday: 9:00 to 17:00
# Tuesday: 9:00 to 17:00
# Wednesday: 9:00-11:30, 12:00-14:00, 14:30-16:30
# Thursday: 9:00 to 17:00
# Friday: 9:00-11:00, 11:30-17:00
eric_busy = {
    0: [(9*60, 17*60)],
    1: [(9*60, 17*60)],
    2: [(9*60, 11*60+30), (12*60, 14*60), (14*60+30, 16*60+30)],
    3: [(9*60, 17*60)],
    4: [(9*60, 11*60), (11*60+30, 17*60)]
}

# Additional preference:
# Eric would like to avoid more meetings on Wednesday.
# This means if any other day is available, choose that one over Wednesday.
# Given Eric's schedule, the only possible days for him are Wednesday and Friday,
# so we prefer Friday.

def no_overlap(busy_start, busy_end, meeting_start, duration):
    # Meeting [meeting_start, meeting_start+duration) does not overlap with busy interval [busy_start, busy_end)
    return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)

def find_earliest_meeting():
    # Possible days that satisfy Eric's availability based on busy intervals:
    # Eric is busy all day on Monday, Tuesday, and Thursday.
    # Thus only Wednesday (2) and Friday (4) are feasible.
    # Since Eric would like to avoid Wednesday, try Friday first.
    candidate_days = [4, 2]
    
    for day in candidate_days:
        solver = Solver()
        # s: meeting start time in minutes from midnight for that day.
        s = Int("s")
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Constrain the meeting time to avoid all busy intervals for Eugene
        if day in eugene_busy:
            for (busy_start, busy_end) in eugene_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Constrain the meeting time to avoid all busy intervals for Eric
        if day in eric_busy:
            for (busy_start, busy_end) in eric_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Iterate over each minute of the work day for a valid meeting start time.
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