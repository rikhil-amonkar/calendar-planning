from constraint import Problem

# Helper functions for time handling
def tm(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours and meeting duration
WORK_START = tm(9, 0)
WORK_END = tm(17, 0)
DURATION = 30

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Busy schedules in minutes since midnight
betty_busy = {
    "Monday":    [(tm(10, 0), tm(10, 30)), (tm(13, 30), tm(14, 0)), (tm(15, 0), tm(15, 30)), (tm(16, 0), tm(16, 30))],
    "Tuesday":   [(tm(9, 0), tm(9, 30)), (tm(11, 30), tm(12, 0)), (tm(12, 30), tm(13, 0)), (tm(13, 30), tm(14, 0)), (tm(16, 30), tm(17, 0))],
    "Wednesday": [(tm(9, 30), tm(10, 30)), (tm(13, 0), tm(13, 30)), (tm(14, 0), tm(14, 30))],
    "Thursday":  [(tm(9, 30), tm(10, 0)), (tm(11, 30), tm(12, 0)), (tm(14, 0), tm(14, 30)), (tm(15, 0), tm(15, 30)), (tm(16, 30), tm(17, 0))]
}

scott_busy = {
    "Monday":    [(tm(9, 30), tm(15, 0)), (tm(15, 30), tm(16, 0)), (tm(16, 30), tm(17, 0))],
    "Tuesday":   [(tm(9, 0), tm(9, 30)), (tm(10, 0), tm(11, 0)), (tm(11, 30), tm(12, 0)), (tm(12, 30), tm(13, 30)), (tm(14, 0), tm(15, 0)), (tm(16, 0), tm(16, 30))],
    "Wednesday": [(tm(9, 30), tm(12, 30)), (tm(13, 0), tm(13, 30)), (tm(14, 0), tm(14, 30)), (tm(15, 0), tm(15, 30)), (tm(16, 0), tm(16, 30))],
    "Thursday":  [(tm(9, 0), tm(9, 30)), (tm(10, 0), tm(10, 30)), (tm(11, 0), tm(12, 0)), (tm(12, 30), tm(13, 0)), (tm(15, 0), tm(16, 0)), (tm(16, 30), tm(17, 0))]
}

# Domain for 30-min start times within work hours
start_times = [t for t in range(WORK_START, WORK_END - DURATION + 1, 30)]

# Constraint problem setup
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

def no_overlap(day, start, busy):
    end = start + DURATION
    for bs, be in busy.get(day, []):
        if start < be and end > bs:
            return False
    return True

# Add busy constraints for both participants
problem.addConstraint(lambda day, start: no_overlap(day, start, betty_busy), ("day", "start"))
problem.addConstraint(lambda day, start: no_overlap(day, start, scott_busy), ("day", "start"))

# Betty's additional constraints:
# - Cannot meet on Monday.
# - On Tuesday and Thursday, cannot meet before 15:00.
def betty_additional(day, start):
    if day == "Monday":
        return False
    if day in ("Tuesday", "Thursday"):
        return start >= tm(15, 0)
    return True

problem.addConstraint(betty_additional, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    print("No solution found.")
else:
    # Preference: Scott would like to avoid Wednesday (soft preference)
    # Choose earliest time, preferring Tuesday/Thursday over Wednesday, Monday last
    preferred_day_order = ["Tuesday", "Thursday", "Wednesday", "Monday"]
    order_index = {d: i for i, d in enumerate(preferred_day_order)}

    best = min(solutions, key=lambda s: (order_index.get(s["day"], 999), s["start"]))

    day = best["day"]
    start = best["start"]
    end = start + DURATION

    # Output day and time range in requested format
    print(day)
    print(f"{{{fmt(start)}:{fmt(end)}}}")