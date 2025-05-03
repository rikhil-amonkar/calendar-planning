from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration in minutes (one hour meeting)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END = 17 * 60      # 17:00 → 1020 minutes

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Alexander would rather not meet on Monday, and Victoria doesn't want to meet on Tuesday.
# So eligible days are Wednesday and Thursday.
candidate_days = [2, 3]

# Busy intervals for Alexander (in minutes after midnight):
# Monday: 11:00-11:30, 13:00-13:30, 16:30-17:00 (not considered since he avoids Monday)
# Tuesday: 9:00-10:30, 12:00-13:00, 13:30-15:00
# Wednesday: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-15:30, 16:00-17:00
# Thursday: 9:00-11:30, 13:00-13:30, 14:30-16:30
alex_busy = {
    # Monday not used
    1: [(9 * 60, 10 * 60 + 30), (12 * 60, 13 * 60), (13 * 60 + 30, 15 * 60)],
    2: [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30),
        (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30),
        (16 * 60, 17 * 60)],
    3: [(9 * 60, 11 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 16 * 60 + 30)]
}

# Busy intervals for Victoria (in minutes after midnight):
# Monday: 9:00-15:00, 16:00-17:00
# Tuesday: 9:00-9:30, 10:30-11:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 16:00-16:30
# Wednesday: 9:00-10:30, 11:00-12:30, 13:00-14:00, 15:00-16:30
# Thursday: 11:30-12:00, 12:30-13:00, 15:30-16:00
vicky_busy = {
    0: [(9 * 60, 15 * 60), (16 * 60, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (12 * 60 + 30, 13 * 60),
        (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (16 * 60, 16 * 60 + 30)],
    2: [(9 * 60, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (13 * 60, 14 * 60),
        (15 * 60, 16 * 60 + 30)],
    3: [(11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (15 * 60 + 30, 16 * 60)]
}

# Utility function: returns a Z3 constraint ensuring the meeting starting at 's' (with 'duration')
# does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest valid meeting time given candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # 's' is the meeting start time in minutes after midnight.
        s = Int("s")
        # The meeting must be within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Alexander's busy intervals if available for the day.
        if day in alex_busy:
            for busy_start, busy_end in alex_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Victoria's busy intervals if available for the day.
        if day in vicky_busy:
            for busy_start, busy_end in vicky_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Test each potential start time in order from earliest to latest.
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