# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

# Helper functions
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def overlaps(start, duration, block):
    s, e = block
    return (start < e) and (start + duration > s)

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
step = 30  # minutes
duration = 30  # minutes

# Participants' busy schedules (Monday)
busy = {
    "Jeffrey": [(to_minutes("09:30"), to_minutes("10:00")),
                (to_minutes("10:30"), to_minutes("11:00"))],
    "Virginia": [(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("10:00"), to_minutes("10:30")),
                 (to_minutes("14:30"), to_minutes("15:00")),
                 (to_minutes("16:00"), to_minutes("16:30"))],
    "Melissa": [(to_minutes("09:00"), to_minutes("11:30")),
                (to_minutes("12:00"), to_minutes("12:30")),
                (to_minutes("13:00"), to_minutes("15:00")),
                (to_minutes("16:00"), to_minutes("17:00"))],
}

# Build domain of possible start times (aligned to 30 minutes, meeting must end by work_end)
domain = [t for t in range(work_start, work_end - duration + 1, step)]

# Set up constraint problem
problem = Problem()
problem.addVariable("start", domain)

# Add busy constraints for each participant
for person, blocks in busy.items():
    def not_overlapping(start, blocks=blocks):
        for b in blocks:
            if overlaps(start, duration, b):
                return False
        return True
    problem.addConstraint(not_overlapping, ("start",))

# Find all feasible solutions
solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Preference: Melissa would rather not meet after 14:00
pref_cutoff = to_minutes("14:00")
preferred = [s for s in solutions if s["start"] <= pref_cutoff]

candidates = preferred if preferred else solutions
chosen = min(candidates, key=lambda s: s["start"])

start_min = chosen["start"]
end_min = start_min + duration

start_str = minutes_to_str(start_min)
end_str = minutes_to_str(end_min)

# Output required: include time range like {HH:MM:HH:MM} and the day of week
print(f"{{{start_str}:{end_str}}}")
print(day)