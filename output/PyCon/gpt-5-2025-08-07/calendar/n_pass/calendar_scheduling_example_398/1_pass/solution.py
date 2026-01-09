# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def no_overlap_constraint(blocks, duration):
    def constraint(t):
        for s, e in blocks:
            if t < e and (t + duration) > s:
                return False
        return True
    return constraint

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' blocked times (Monday)
Doris_blocks = [
    (to_minutes("09:00"), to_minutes("11:00")),
    (to_minutes("13:30"), to_minutes("14:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]
Theresa_blocks = [
    (to_minutes("10:00"), to_minutes("12:00")),
]
Christian_blocks = []  # no meetings
Terry_blocks = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("13:30"), to_minutes("14:00")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("15:30"), to_minutes("17:00")),
]
Carolyn_blocks = [
    (to_minutes("09:00"), to_minutes("10:30")),
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("12:00"), to_minutes("13:00")),
    (to_minutes("13:30"), to_minutes("14:30")),
    (to_minutes("15:00"), to_minutes("17:00")),
]
Kyle_blocks = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("14:30"), to_minutes("17:00")),
]

# Build domain of possible start times (every 30 minutes within work hours)
domain = []
t = work_start
while t + duration <= work_end:
    domain.append(t)
    t += 30  # 30-minute granularity

problem = Problem()
problem.addVariable("start", domain)

# Work hours constraint (redundant due to domain, but kept for clarity)
problem.addConstraint(lambda t: work_start <= t and (t + duration) <= work_end, ["start"])

# Participant availability constraints
problem.addConstraint(no_overlap_constraint(Doris_blocks, duration), ["start"])
problem.addConstraint(no_overlap_constraint(Theresa_blocks, duration), ["start"])
problem.addConstraint(no_overlap_constraint(Christian_blocks, duration), ["start"])
problem.addConstraint(no_overlap_constraint(Terry_blocks, duration), ["start"])
problem.addConstraint(no_overlap_constraint(Carolyn_blocks, duration), ["start"])
problem.addConstraint(no_overlap_constraint(Kyle_blocks, duration), ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible time found.")

# Choose the earliest feasible start time
best = min(solutions, key=lambda s: s["start"])
start = best["start"]
end = start + duration

time_range_str = f"{fmt_minutes(start)}:{fmt_minutes(end)}"

# Output must include both the time range in braces and the day of the week
print(f"{{{time_range_str}}}")
print(day)