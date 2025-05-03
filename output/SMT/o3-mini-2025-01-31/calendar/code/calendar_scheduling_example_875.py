from z3 import Solver, Int, Or, sat

# Meeting parameters
duration = 60            # meeting duration in minutes (1 hour)
WORK_START = 9 * 60      # 9:00 in minutes (540)
WORK_END   = 17 * 60     # 17:00 in minutes (1020)

# We encode days as: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
candidate_days = [0, 1, 2, 3]

# Define busy schedules (times are in minutes from midnight)

# Natalie's busy schedule:
natalie_busy = {
    0: [ (9 * 60, 9 * 60 + 30),         # Monday: 9:00 - 9:30  => (540,570)
         (10 * 60, 12 * 60),            # Monday: 10:00 - 12:00 => (600,720)
         (12 * 60 + 30, 13 * 60),       # Monday: 12:30 - 13:00 => (750,780)
         (14 * 60, 14 * 60 + 30),       # Monday: 14:00 - 14:30 => (840,870)
         (15 * 60, 16 * 60 + 30)],      # Monday: 15:00 - 16:30 => (900,990)
    1: [ (9 * 60, 9 * 60 + 30),         # Tuesday: 9:00 - 9:30   => (540,570)
         (10 * 60, 10 * 60 + 30),       # Tuesday: 10:00 - 10:30 => (600,630)
         (12 * 60 + 30, 14 * 60),       # Tuesday: 12:30 - 14:00 => (750,840)
         (16 * 60, 17 * 60)],           # Tuesday: 16:00 - 17:00 => (960,1020)
    2: [ (11 * 60, 11 * 60 + 30),       # Wednesday: 11:00 - 11:30 => (660,690)
         (16 * 60, 16 * 60 + 30)],      # Wednesday: 16:00 - 16:30 => (960,990)
    3: [ (10 * 60, 11 * 60),            # Thursday: 10:00 - 11:00 => (600,660)
         (11 * 60 + 30, 15 * 60),       # Thursday: 11:30 - 15:00 => (690,900)
         (15 * 60 + 30, 16 * 60),       # Thursday: 15:30 - 16:00 => (930,960)
         (16 * 60 + 30, 17 * 60)],      # Thursday: 16:30 - 17:00 => (990,1020)
}

# William's busy schedule:
william_busy = {
    0: [ (9 * 60 + 30, 11 * 60),        # Monday: 9:30 - 11:00 => (570,660)
         (11 * 60 + 30, 17 * 60)],      # Monday: 11:30 - 17:00 => (690,1020)
    1: [ (9 * 60, 13 * 60),             # Tuesday: 9:00 - 13:00 => (540,780)
         (13 * 60 + 30, 16 * 60)],      # Tuesday: 13:30 - 16:00 => (810,960)
    2: [ (9 * 60, 12 * 60 + 30),        # Wednesday: 9:00 - 12:30 => (540,750)
         (13 * 60, 14 * 60 + 30),       # Wednesday: 13:00 - 14:30 => (780,870)
         (15 * 60 + 30, 16 * 60),       # Wednesday: 15:30 - 16:00 => (930,960)
         (16 * 60 + 30, 17 * 60)],      # Wednesday: 16:30 - 17:00 => (990,1020)
    3: [ (9 * 60, 10 * 60 + 30),        # Thursday: 9:00 - 10:30 => (540,630)
         (11 * 60, 11 * 60 + 30),       # Thursday: 11:00 - 11:30 => (660,690)
         (12 * 60, 12 * 60 + 30),       # Thursday: 12:00 - 12:30 => (720,750)
         (13 * 60, 14 * 60),            # Thursday: 13:00 - 14:00 => (780,840)
         (15 * 60, 17 * 60)],           # Thursday: 15:00 - 17:00 => (900,1020)
}

# Utility function: For a meeting start time 's' (lasting duration minutes),
# ensure it does not overlap a busy interval [busy_start, busy_end)
def no_overlap(busy_start, busy_end, s):
    return Or(s + duration <= busy_start, s >= busy_end)

# Function to find an available meeting time on one of the candidate days.
def find_meeting_time(days):
    for day in days:
        solver = Solver()
        s = Int("s")  # meeting start time in minutes from midnight
        solver.add(s >= WORK_START, s + duration <= WORK_END)
        
        # Add constraints for Natalie's busy intervals on this day.
        for busy_start, busy_end in natalie_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Add constraints for William's busy intervals on this day.
        for busy_start, busy_end in william_busy.get(day, []):
            solver.add(no_overlap(busy_start, busy_end, s))
        
        # Try each minute in the work hours and pick the earliest valid time.
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
    start_hour, start_minute = divmod(selected_start, 60)
    end_hour, end_minute = divmod(selected_end, 60)
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    print("A valid meeting time is on {} from {:02d}:{:02d} to {:02d}:{:02d}.".
          format(day_names[selected_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time could be found that satisfies all constraints.")