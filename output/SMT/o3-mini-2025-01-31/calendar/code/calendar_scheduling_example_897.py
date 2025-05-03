from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60            # meeting duration in minutes (1 hour meeting)
WORK_START = 9 * 60      # 9:00 in minutes (540)
WORK_END = 17 * 60       # 17:00 in minutes (1020)

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
candidate_days = [0, 1, 2, 3]

# Gabriel's busy intervals (in minutes after midnight):
# Monday: 9:30 to 10:30, 12:30 to 14:00, 15:00 to 15:30
# Tuesday: 11:00 to 11:30, 12:00 to 12:30
# Wednesday: 9:30 to 10:00, 12:00 to 12:30
# Thursday: 10:00 to 11:00, 11:30 to 12:00, 16:30 to 17:00
gabriel_busy = {
    0: [(9 * 60 + 30, 10 * 60 + 30),
        (12 * 60 + 30, 14 * 60),
        (15 * 60, 15 * 60 + 30)],
    1: [(11 * 60, 11 * 60 + 30),
        (12 * 60, 12 * 60 + 30)],
    2: [(9 * 60 + 30, 10 * 60),
        (12 * 60, 12 * 60 + 30)],
    3: [(10 * 60, 11 * 60),
        (11 * 60 + 30, 12 * 60),
        (16 * 60 + 30, 17 * 60)]
}

# Cynthia's busy intervals (in minutes after midnight):
# Monday: 9:00 to 12:30, 13:00 to 13:30, 14:00 to 17:00
# Tuesday: 9:00 to 17:00
# Wednesday: 9:00 to 10:00, 11:00 to 13:00, 13:30 to 17:00
# Thursday: 9:00 to 16:00, 16:30 to 17:00
cynthia_busy = {
    0: [(9 * 60, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30),
        (14 * 60, 17 * 60)],
    1: [(9 * 60, 17 * 60)],
    2: [(9 * 60, 10 * 60),
        (11 * 60, 13 * 60),
        (13 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 16 * 60),
        (16 * 60 + 30, 17 * 60)]
}

# Utility function: returns a Z3 constraint ensuring that a meeting starting at time 's' with 'duration'
# does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time among candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # 's' represents the meeting start time (in minutes after midnight)
        s = Int("s")
        # Meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Gabriel's constraints for the day.
        if day in gabriel_busy:
            for busy_start, busy_end in gabriel_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Cynthia's constraints for the day.
        if day in cynthia_busy:
            for busy_start, busy_end in cynthia_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Try every possible start time from the earliest to the latest possible.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    selected_day = day_names[day]
    selected_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(selected_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")