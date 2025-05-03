from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60           # meeting duration is 60 minutes (1 hour)
WORK_START = 9 * 60     # 9:00 in minutes => 540
WORK_END = 17 * 60      # 17:00 in minutes => 1020

# Days encoding:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
# Lori would like to avoid more meetings on Friday, so we choose candidate days as Monday to Thursday.
candidate_days = [0, 1, 2, 3]

# Jeremy's busy intervals (each tuple is (start, end) in minutes after midnight):
jeremy_busy = {
    0: [(12 * 60, 13 * 60 + 30), (14 * 60 + 30, 16 * 60 + 30)],  # Monday: 12:00-13:30, 14:30-16:30
    1: [(9 * 60, 10 * 60), (11 * 60, 11 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],  # Tuesday
    2: [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (16 * 60, 16 * 60 + 30)],  # Wednesday
    3: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), 
        (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],  # Thursday
    4: [(9 * 60, 9 * 60 + 30), (16 * 60 + 30, 17 * 60)]  # Friday (not used)
}

# Lori's busy intervals (each tuple is (start, end) in minutes after midnight):
lori_busy = {
    0: [(14 * 60 + 30, 17 * 60)],  # Monday: 14:30-17:00
    1: [(9 * 60, 11 * 60), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60, 17 * 60)],  # Tuesday
    2: [(9 * 60, 10 * 60), (10 * 60 + 30, 13 * 60 + 30), (14 * 60, 17 * 60)],  # Wednesday
    3: [(9 * 60, 11 * 60 + 30), (12 * 60 + 30, 17 * 60)],  # Thursday
    4: [(9 * 60 + 30, 13 * 60), (13 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)]  # Friday (not used)
}

# Utility function: returns a Z3 constraint that ensures a meeting starting at 's' with length 'duration'
# does NOT overlap with a busy interval (busy_start, busy_end)
def no_overlap(busy_start, busy_end, s, duration):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time on the candidate days
def find_meeting_time(days):
    # We iterate over days in order and try to schedule at the earliest possible start time.
    for day in days:
        solver = Solver()
        # 's' represents the meeting start time (in minutes after midnight)
        s = Int("s")
        # The meeting must take place entirely within working hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add Jeremy's busy constraints for the given day.
        if day in jeremy_busy:
            for busy_start, busy_end in jeremy_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Add Lori's busy constraints for the given day.
        if day in lori_busy:
            for busy_start, busy_end in lori_busy[day]:
                solver.add(no_overlap(busy_start, busy_end, s, duration))
        
        # Check every possible start time (in minutes) from WORK_START to latest possible start.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

day, t = find_meeting_time(candidate_days)

if day is not None:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    selected_day = day_names[day]
    meeting_end = t + duration
    start_hr, start_min = divmod(t, 60)
    end_hr, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(selected_day, start_hr, start_min, end_hr, end_min))
else:
    print("No valid meeting time could be found that satisfies all constraints.")