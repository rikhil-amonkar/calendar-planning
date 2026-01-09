# Requires: python-constraint (pip install python-constraint)
from constraint import Problem

def t(h, m):
    return h * 60 + m

def minutes_to_hhmm(x):
    return f"{x // 60:02d}:{x % 60:02d}"

# Meeting parameters
DAY = "Monday"
WORK_START = t(9, 0)
WORK_END = t(17, 0)
DURATION = 30  # minutes

# Participants' busy schedules for Monday (start, end) in minutes since 00:00
busy = {
    "Andrew": [],
    "Grace": [],
    "Samuel": [
        (t(9, 0), t(10, 30)),
        (t(11, 30), t(12, 0)),
        (t(13, 0), t(13, 30)),
        (t(14, 0), t(16, 0)),
        (t(16, 30), t(17, 0)),
    ],
}

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and b_start < a_end

# Build the constraint problem
problem = Problem()

# Domain: candidate start times in 30-minute increments within work hours
domain = list(range(WORK_START, WORK_END - DURATION + 1, 30))
problem.addVariable("start", domain)

# Constraints: meeting must not overlap with any participant's busy block
for person, blocks in busy.items():
    def make_constraint(blocks_ref):
        def constraint(start):
            end = start + DURATION
            # Ensure within work hours (redundant due to domain, but safe)
            if start < WORK_START or end > WORK_END:
                return False
            for bs, be in blocks_ref:
                if overlaps(start, end, bs, be):
                    return False
            return True
        return constraint
    problem.addConstraint(make_constraint(blocks), ("start",))

solutions = problem.getSolutions()

if not solutions:
    print("No feasible meeting time found.")
else:
    # Earliest availability
    best = min(solutions, key=lambda s: s["start"])
    start = best["start"]
    end = start + DURATION
    time_range = f"{minutes_to_hhmm(start)}:{minutes_to_hhmm(end)}"
    print(f"{DAY} {{{time_range}}}")