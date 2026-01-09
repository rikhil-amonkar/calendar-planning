from constraint import Problem

# Utility functions
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_timestr(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Meeting parameters
day_name = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes
slot_step = 30  # minutes

# Participants' busy schedules (inclusive start, exclusive end)
busy_str = {
    "Megan":     [("09:00","09:30"), ("10:00","11:00"), ("12:00","12:30")],
    "Christine": [("09:00","09:30"), ("11:30","12:00"), ("13:00","14:00"), ("15:30","16:30")],
    "Gabriel":   [],
    "Sara":      [("11:30","12:00"), ("14:30","15:00")],
    "Bruce":     [("09:30","10:00"), ("10:30","12:00"), ("12:30","14:00"), ("14:30","15:00"), ("15:30","16:30")],
    "Kathryn":   [("10:00","15:30"), ("16:00","16:30")],
    "Billy":     [("09:00","09:30"), ("11:00","11:30"), ("12:00","14:00"), ("14:30","15:30")],
}

# Convert busy schedules to minutes
busy = {}
for person, intervals in busy_str.items():
    busy[person] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Build domain of possible start times
domain = list(range(work_start, work_end - duration + 1, slot_step))

# Create constraint problem
problem = Problem()
problem.addVariable("slot", domain)

# Add availability constraints per participant
def make_availability_constraint(intervals):
    def is_available(slot):
        start = slot
        end = slot + duration
        for bs, be in intervals:
            # If intervals overlap, not available
            if not (end <= bs or start >= be):
                return False
        return True
    return is_available

for person, intervals in busy.items():
    problem.addConstraint(make_availability_constraint(intervals), ("slot",))

# Solve and pick an earliest valid time
solutions = problem.getSolutions()
if not solutions:
    raise RuntimeError("No feasible meeting time found.")
best = min(solutions, key=lambda s: s["slot"])
start_min = best["slot"]
end_min = start_min + duration

start_str = to_timestr(start_min)
end_str = to_timestr(end_min)

# Output: time range in {HH:MM:HH:MM} and the day of the week
print(f"{{{start_str}:{end_str}}}")
print(day_name)