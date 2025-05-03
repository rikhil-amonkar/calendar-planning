from z3 import Solver, Int, Or, sat

# Meeting duration: 1 hour = 60 minutes
duration = 60

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
WORK_START = 9 * 60    # 540
WORK_END   = 17 * 60   # 1020

# Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Abigail's busy schedule (in minutes from midnight)
abigail_busy = {
    0: [ (9 * 60, 10 * 60),         # Monday: 9:00-10:00 -> [540,600)
         (12 * 60 + 30, 13 * 60 + 30), # Monday: 12:30-13:30 -> [750,810)
         (15 * 60 + 30, 16 * 60),     # Monday: 15:30-16:00 -> [930,960)
         (16 * 60 + 30, 17 * 60) ],   # Monday: 16:30-17:00 -> [990,1020)
    1: [ (9 * 60, 10 * 60),         # Tuesday: 9:00-10:00 -> [540,600)
         (11 * 60 + 30, 12 * 60),     # Tuesday: 11:30-12:00 -> [690,720)
         (13 * 60, 13 * 60 + 30),     # Tuesday: 13:00-13:30 -> [780,810)
         (15 * 60, 15 * 60 + 30) ],   # Tuesday: 15:00-15:30 -> [900,930)
    2: [ (9 * 60 + 30, 10 * 60),     # Wednesday: 9:30-10:00 -> [570,600)
         (10 * 60 + 30, 12 * 60),     # Wednesday: 10:30-12:00 -> [630,720)
         (14 * 60, 15 * 60),          # Wednesday: 14:00-15:00 -> [840,900)
         (16 * 60, 16 * 60 + 30) ],   # Wednesday: 16:00-16:30 -> [960,990)
    3: [ (11 * 60, 12 * 60),         # Thursday: 11:00-12:00 -> [660,720)
         (14 * 60, 14 * 60 + 30),     # Thursday: 14:00-14:30 -> [840,870)
         (16 * 60, 16 * 60 + 30) ]    # Thursday: 16:00-16:30 -> [960,990)
}

# Sara's busy schedule (in minutes from midnight)
sara_busy = {
    0: [ (9 * 60, 11 * 60 + 30),    # Monday: 9:00-11:30 -> [540,690)
         (12 * 60, 13 * 60 + 30),    # Monday: 12:00-13:30 -> [720,810)
         (14 * 60 + 30, 17 * 60) ],  # Monday: 14:30-17:00 -> [870,1020)
    1: [ (9 * 60, 10 * 60 + 30),     # Tuesday: 9:00-10:30 -> [540,630)
         (11 * 60, 17 * 60) ],       # Tuesday: 11:00-17:00 -> [660,1020)
    2: [ (9 * 60, 10 * 60 + 30),     # Wednesday: 9:00-10:30 -> [540,630)
         (11 * 60, 14 * 60 + 30),     # Wednesday: 11:00-14:30 -> [660,870)
         (15 * 60 + 30, 16 * 60),     # Wednesday: 15:30-16:00 -> [930,960)
         (16 * 60 + 30, 17 * 60) ],   # Wednesday: 16:30-17:00 -> [990,1020)
    3: [ (9 * 60, 9 * 60 + 30),      # Thursday: 9:00-9:30 -> [540,570)
         (10 * 60, 13 * 60 + 30),     # Thursday: 10:00-13:30 -> [600,810)
         (14 * 60, 17 * 60) ]         # Thursday: 14:00-17:00 -> [840,1020)
}

# Helper function: Ensures the meeting [s, s+duration) does NOT overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find the earliest meeting time that satisfies all constraints.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        
        # Meeting must occur within work hours.
        solver.add(s >= WORK_START, s + duration <= WORK_END)

        # Add Abigail's busy constraints for the day.
        for interval in abigail_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Add Sara's busy constraints for the day.
        for interval in sara_busy.get(day, []):
            busy_start, busy_end = interval
            solver.add(no_overlap(busy_start, busy_end, s))
            
        # Try all possible start times (minute-by-minute) between WORK_START and last possible start.
        for t in range(WORK_START, WORK_END - duration + 1):
            solver.push()
            solver.add(s == t)
            if solver.check() == sat:
                return day, t
            solver.pop()
    return None, None

selected_day, selected_start = find_meeting_time(candidate_days)

if selected_day is not None:
    selected_end = selected_start + duration
    # Convert minutes to HH:MM format.
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}."
          .format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")