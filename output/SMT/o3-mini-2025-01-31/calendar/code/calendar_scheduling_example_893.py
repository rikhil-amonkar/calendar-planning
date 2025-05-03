from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half hour meeting)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END = 17 * 60      # 17:00 → 1020 minutes

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Michelle does not want to meet on Tuesday.
# Also note that Julie is busy all day on Monday.
# Thus, we only consider Wednesday and Thursday.
candidate_days = [2, 3]

# Busy intervals for Michelle (times in minutes after midnight):
# Monday: 11:00-11:30, 14:30-15:00, 15:30-16:00
# Tuesday: 10:00-10:30, 11:30-12:30, 14:30-15:00, 15:30-16:00
# Wednesday: 10:00-10:30, 15:00-16:00
# Thursday: 11:00-11:30, 13:30-14:00, 14:30-15:00, 15:30-16:30
michelle_busy = {
    0: [(11*60, 11*60+30), (14*60+30, 15*60), (15*60+30, 16*60)],
    1: [(10*60, 10*60+30), (11*60+30, 12*60+30), (14*60+30, 15*60), (15*60+30, 16*60)],
    2: [(10*60, 10*60+30), (15*60, 16*60)],
    3: [(11*60, 11*60+30), (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 16*60+30)]
}

# Busy intervals for Julie (times in minutes after midnight):
# Monday: 9:00-17:00 (all day busy)
# Tuesday: 11:00-12:00, 12:30-13:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
# Wednesday: 9:00-9:30, 10:00-13:30, 14:00-15:00, 16:00-17:00
# Thursday: 9:00-10:00, 11:00-12:30, 14:00-15:00, 15:30-17:00
julie_busy = {
    0: [(9*60, 17*60)],
    1: [(11*60, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (15*60+30, 16*60), (16*60+30, 17*60)],
    2: [(9*60, 9*60+30), (10*60, 13*60+30), (14*60, 15*60), (16*60, 17*60)],
    3: [(9*60, 10*60), (11*60, 12*60+30), (14*60, 15*60), (15*60+30, 17*60)]
}

# Utility function: returns a Z3 constraint that ensures a meeting starting at 's'
# with length 'duration' does NOT overlap with a busy interval (busy_start, busy_end).
def no_overlap(busy_start, busy_end, s, duration):
    # either the meeting ends no later than busy_start or starts no earlier than busy_end
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest valid meeting time given candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # s is the meeting start time in minutes after midnight
        s = Int("s")
        
        # The meeting must fit within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Michelle's busy time constraints for the given day.
        if day in michelle_busy:
            for busy_start, busy_end in michelle_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Julie's busy time constraints for the given day.
        if day in julie_busy:
            for busy_start, busy_end in julie_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Try each possible start time in earliest-first order.
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