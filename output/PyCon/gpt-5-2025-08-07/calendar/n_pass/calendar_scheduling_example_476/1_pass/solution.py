from constraint import Problem

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Meeting parameters
DAY = "Monday"
WORK_START = to_minutes(9, 0)
WORK_END = to_minutes(17, 0)
DURATION = 30  # minutes

# Busy schedules (inclusive start, exclusive end) in minutes from 00:00
busy = {
    "Daniel": [],
    "Kathleen": [(to_minutes(14,30), to_minutes(15,30))],
    "Carolyn": [(to_minutes(12,0), to_minutes(12,30)),
                (to_minutes(13,0), to_minutes(13,30))],
    "Roger": [],  # Preference handled as a separate constraint
    "Cheryl": [(to_minutes(9,0), to_minutes(9,30)),
               (to_minutes(10,0), to_minutes(11,30)),
               (to_minutes(12,30), to_minutes(13,30)),
               (to_minutes(14,0), to_minutes(17,0))],
    "Virginia": [(to_minutes(9,30), to_minutes(11,30)),
                 (to_minutes(12,0), to_minutes(12,30)),
                 (to_minutes(13,0), to_minutes(13,30)),
                 (to_minutes(14,30), to_minutes(15,30)),
                 (to_minutes(16,0), to_minutes(17,0))],
    "Angela": [(to_minutes(9,30), to_minutes(10,0)),
               (to_minutes(10,30), to_minutes(11,30)),
               (to_minutes(12,0), to_minutes(12,30)),
               (to_minutes(13,0), to_minutes(13,30)),
               (to_minutes(14,0), to_minutes(16,30))],
}

# Create domain of possible start times (every 30 minutes within work hours)
start_times = list(range(WORK_START, WORK_END - DURATION + 1, 30))

problem = Problem()
problem.addVariable("start", start_times)

def no_overlap_constraint(person_intervals):
    def _constraint(start):
        meeting_start = start
        meeting_end = start + DURATION
        for s, e in person_intervals:
            if meeting_start < e and meeting_end > s:
                return False
        return True
    return _constraint

# Add constraints for each participant's busy times
for person, intervals in busy.items():
    problem.addConstraint(no_overlap_constraint(intervals), ("start",))

# Roger's preference: not before 12:30
problem.addConstraint(lambda start: start >= to_minutes(12, 30), ("start",))

# Solve and select the earliest valid time
solutions = problem.getSolutions()
if not solutions:
    raise RuntimeError("No feasible meeting time found, but the task states a solution exists.")

best_start = min(sol["start"] for sol in solutions)
best_end = best_start + DURATION

# Output the result
print(f"{{{fmt_time(best_start)}:{fmt_time(best_end)}}}")
print(DAY)