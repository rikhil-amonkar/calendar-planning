from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration in minutes (one hour meeting)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END = 17 * 60      # 17:00 → 1020 minutes

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Ann does not want to meet on Monday and Thursday.
# Sharon does not want to meet on Tuesday.
# Thus the only candidate day is Wednesday.
candidate_days = [2]

# Busy intervals for Ann (in minutes after midnight):
# Monday: 11:30 to 12:00, 13:00 to 13:30, 16:00 to 17:00
# Tuesday: 11:30 to 12:00
# Wednesday: 11:00 to 11:30
ann_busy = {
    0: [(11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(11 * 60 + 30, 12 * 60)],
    2: [(11 * 60, 11 * 60 + 30)]
}

# Busy intervals for Sharon (in minutes after midnight):
# Monday: 9:00 to 10:30, 11:30 to 12:00, 13:00 to 13:30, 14:00 to 15:30, 16:00 to 17:00
# Tuesday: 9:30 to 10:00, 10:30 to 11:30, 12:00 to 13:00, 14:00 to 15:30, 16:30 to 17:00
# Wednesday: 10:00 to 11:00, 11:30 to 13:30, 14:00 to 15:00, 15:30 to 16:30
# Thursday: 10:00 to 16:00, 16:30 to 17:00
sharon_busy = {
    0: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30),
        (14 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 13 * 60),
        (14 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    2: [(10 * 60, 11 * 60), (11 * 60 + 30, 13 * 60 + 30), (14 * 60, 15 * 60),
        (15 * 60 + 30, 16 * 60 + 30)],
    3: [(10 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Utility function: returns a Z3 constraint ensuring the meeting start time 's'
# with 'duration' does not overlap with a busy interval defined by (busy_start, busy_end).
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest valid meeting time among the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # 's' represents the meeting start time in minutes after midnight.
        s = Int("s")
        # Constrain meeting to be within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Ann's busy intervals for the day.
        if day in ann_busy:
            for busy_start, busy_end in ann_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Sharon's busy intervals for the day.
        if day in sharon_busy:
            for busy_start, busy_end in sharon_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Iterate through each possible start time from earliest to latest.
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
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".
          format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")