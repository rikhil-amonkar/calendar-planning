# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def t(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Work hours and meeting duration
WORK_DAY = "Monday"
WORK_START = t("09:00")
WORK_END = t("17:00")
DURATION = 30  # minutes
SLOT_STEP = 30

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Katherine": [(t("12:00"), t("12:30")), (t("13:00"), t("14:30"))],
    "Rebecca":   [],
    "Julie":     [(t("09:00"), t("09:30")), (t("10:30"), t("11:00")),
                  (t("13:30"), t("14:00")), (t("15:00"), t("15:30"))],
    "Angela":    [(t("09:00"), t("10:00")), (t("10:30"), t("11:00")),
                  (t("11:30"), t("14:00")), (t("14:30"), t("15:00")),
                  (t("16:30"), t("17:00"))],
    "Nicholas":  [(t("09:30"), t("11:00")), (t("11:30"), t("13:30")),
                  (t("14:00"), t("16:00")), (t("16:30"), t("17:00"))],
    "Carl":      [(t("09:00"), t("11:00")), (t("11:30"), t("12:30")),
                  (t("13:00"), t("14:30")), (t("15:00"), t("16:00")),
                  (t("16:30"), t("17:00"))],
}

# Domain of possible start times
allowed_starts = list(range(WORK_START, WORK_END - DURATION + 1, SLOT_STEP))

def no_overlap(start, intervals):
    meeting_start = start
    meeting_end = start + DURATION
    for s, e in intervals:
        if meeting_start < e and meeting_end > s:
            return False
    return True

# Build constraint problem
problem = Problem()
problem.addVariable("start", allowed_starts)

# Add no-overlap constraints for each participant
for person, intervals in busy.items():
    problem.addConstraint(lambda start, ivals=intervals: no_overlap(start, ivals), ("start",))

# Get all feasible solutions within work hours
solutions = problem.getSolutions()

# Respect Angela's preference to avoid meetings before 15:00 when possible
preferred_after = t("15:00")
preferred = [s for s in solutions if s["start"] >= preferred_after]
candidates = preferred if preferred else solutions

# Choose the earliest suitable time
chosen = min(candidates, key=lambda s: s["start"])
start = chosen["start"]
end = start + DURATION

# Output: include both the time range and the day of the week
print(WORK_DAY)
print(f"{{{fmt(start)}:{fmt(end)}}}")