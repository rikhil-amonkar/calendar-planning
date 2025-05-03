from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 30           # meeting duration in minutes (half hour meeting)
WORK_START = 9 * 60     # 9:00 → 540 minutes
WORK_END = 17 * 60      # 17:00 → 1020 minutes

# Days encoding:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# Jean does not want to meet on Monday.
# Thus, although the meeting could be scheduled on any day, we remove Monday.
candidate_days = [1, 2, 3]

# Busy intervals for Lisa (in minutes after midnight):
# Monday: 9:00 to 10:30
# Tuesday: 10:30 to 11:00, 11:30 to 12:00
# Wednesday: 13:00 to 13:30, 15:00 to 15:30
# Thursday: 9:00 to 9:30, 12:30 to 13:00, 13:30 to 14:00, 16:00 to 17:00
lisa_busy = {
    0: [(9 * 60, 10 * 60 + 30)],               # 540 to 630
    1: [(10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60)],  # 630-660, 690-720
    2: [(13 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30)],  # 780-810, 900-930
    3: [(9 * 60, 9 * 60 + 30), (12 * 60 + 30, 13 * 60), 
        (13 * 60 + 30, 14 * 60), (16 * 60, 17 * 60)]         # 540-570, 750-780, 810-840, 960-1020
}

# Busy intervals for Jean (in minutes after midnight):
# Monday: 9:00 to 15:30, 16:30 to 17:00
# Tuesday: 9:00 to 17:00
# Wednesday: 9:00 to 13:30, 14:30 to 17:00
# Thursday: 9:00 to 17:00
jean_busy = {
    0: [(9 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],    # 540-930, 990-1020
    1: [(9 * 60, 17 * 60)],                                    # 540-1020
    2: [(9 * 60, 13 * 60 + 30), (14 * 60 + 30, 17 * 60)],       # 540-810, 870-1020
    3: [(9 * 60, 17 * 60)]                                     # 540-1020
}

# Utility function: returns a constraint that ensures a meeting starting at 's'
# with length 'duration' does not overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest valid meeting time given candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        # Define the meeting start time (in minutes after midnight)
        s = Int("s")
        # Meeting must be entirely within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Lisa's busy-time constraints for the given day.
        if day in lisa_busy:
            for busy_start, busy_end in lisa_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Add Jean's busy-time constraints for the given day.
        if day in jean_busy:
            for busy_start, busy_end in jean_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
                
        # Iterate over possible times (earliest first) to find a valid start time.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()       # save state
            solver.add(s == t)  # try a specific start time
            if solver.check() == sat:
                return day, t
            solver.pop()        # backtrack if unsat
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