# Requires: python-constraint
from constraint import Problem, AllEqualConstraint

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def generate_slots(start_min, end_min, step, duration):
    # Returns possible start times so that [start, start+duration) lies within [start_min, end_min)
    return [s for s in range(start_min, end_min - duration + 1, step)]

def filter_available(slots, blocks, duration):
    # Keep slots that do not overlap any blocked interval
    def overlaps(s, d, bstart, bend):
        return not (s + d <= bstart or s >= bend)
    avail = []
    for s in slots:
        ok = True
        for bstart, bend in blocks:
            if overlaps(s, duration, bstart, bend):
                ok = False
                break
        if ok:
            avail.append(s)
    return avail

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
step = 30  # minutes
duration = 30  # minutes

# Participants' blocked intervals (inclusive of start, exclusive of end)
margaret_blocks = [
    (to_minutes("09:00"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("15:00"), to_minutes("15:30")),
]

donna_blocks = [
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

helen_blocks = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:00"), to_minutes("11:30")),
    (to_minutes("13:00"), to_minutes("14:00")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("15:30"), to_minutes("17:00")),
]

# Generate candidate start slots within work hours
all_slots = generate_slots(work_start, work_end, step, duration)

# Filter availability per participant
margaret_avail = filter_available(all_slots, margaret_blocks, duration)
donna_avail = filter_available(all_slots, donna_blocks, duration)

# Helen's preference: "do not want to meet on Monday after 13:30" -> meeting must end by 13:30
helen_latest_end = to_minutes("13:30")
helen_time_cap = [s for s in all_slots if s + duration <= helen_latest_end]
helen_avail_pref = filter_available(helen_time_cap, helen_blocks, duration)

# Build CSP
problem = Problem()
problem.addVariable("Margaret", margaret_avail)
problem.addVariable("Donna", donna_avail)
problem.addVariable("Helen", helen_avail_pref)
problem.addConstraint(AllEqualConstraint(), ["Margaret", "Donna", "Helen"])

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found, but a solution was expected.")

# Choose the earliest feasible time
best = min(solutions, key=lambda s: s["Margaret"])
start_min = best["Margaret"]
end_min = start_min + duration

start_str = to_hhmm(start_min)
end_str = to_hhmm(end_min)

print(day)
print(f"{{{start_str}:{end_str}}}")