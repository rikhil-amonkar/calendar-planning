# Requires: python-constraint (pip install python-constraint)
from constraint import Problem

def minutes(h, m):
    return h * 60 + m

def format_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
WORK_START = minutes(9, 0)
WORK_END = minutes(17, 0)
DURATION = 30  # minutes

# Days considered
all_days = ["Monday", "Tuesday", "Wednesday"]

# Participant schedules (busy times per day)
busy = {
    "Arthur": {
        "Monday": [
            (minutes(11, 0), minutes(11, 30)),
            (minutes(13, 30), minutes(14, 0)),
            (minutes(15, 0), minutes(15, 30)),
        ],
        "Tuesday": [
            (minutes(13, 0), minutes(13, 30)),
            (minutes(16, 0), minutes(16, 30)),
        ],
        "Wednesday": [
            (minutes(10, 0), minutes(10, 30)),
            (minutes(11, 0), minutes(11, 30)),
            (minutes(12, 0), minutes(12, 30)),
            (minutes(14, 0), minutes(14, 30)),
            (minutes(16, 0), minutes(16, 30)),
        ],
    },
    "Michael": {
        "Monday": [
            (minutes(9, 0), minutes(12, 0)),
            (minutes(12, 30), minutes(13, 0)),
            (minutes(14, 0), minutes(14, 30)),
            (minutes(15, 0), minutes(17, 0)),
        ],
        "Tuesday": [
            (minutes(9, 30), minutes(11, 30)),
            (minutes(12, 0), minutes(13, 30)),
            (minutes(14, 0), minutes(15, 30)),
        ],
        "Wednesday": [
            (minutes(10, 0), minutes(12, 30)),
            (minutes(13, 0), minutes(13, 30)),
        ],
    },
}

# Constraints:
# - Meeting between 9:00 and 17:00
# - Duration 30 minutes
# - Days: Monday, Tuesday, Wednesday
# - Arthur cannot meet on Tuesday
allowed_days = ["Monday", "Wednesday"]  # Arthur cannot meet Tuesday

# Build problem
problem = Problem()
start_domain = list(range(WORK_START, WORK_END - DURATION + 1, 30))
problem.addVariable("day", allowed_days)
problem.addVariable("start", start_domain)

def make_availability_constraint(person_busy):
    def constraint(day, start):
        end = start + DURATION
        # Check against person's busy times on the chosen day
        for b_start, b_end in person_busy.get(day, []):
            # No overlap: [start, end) does not intersect [b_start, b_end)
            if not (end <= b_start or start >= b_end):
                return False
        return True
    return constraint

# Add availability constraints for each participant
problem.addConstraint(make_availability_constraint(busy["Arthur"]), ("day", "start"))
problem.addConstraint(make_availability_constraint(busy["Michael"]), ("day", "start"))

# Find all feasible solutions
solutions = problem.getSolutions()

# Choose earliest by day order (Mon < Tue < Wed) and then by time
day_order = {d: i for i, d in enumerate(all_days)}
solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))

if not solutions:
    # As per the prompt, a solution exists; this is a guard.
    raise RuntimeError("No feasible meeting time found.")

best = solutions[0]
start_str = format_hhmm(best["start"])
end_str = format_hhmm(best["start"] + DURATION)

# Output: time range in {HH:MM:HH:MM} and day of week
print(f"{{{start_str}:{end_str}}}")
print(best["day"])