from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Meeting parameters
meeting_duration = 30  # minutes
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")

# Participants' busy schedules (on Monday)
schedules = {
    "Lisa": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("14:00"), to_minutes("16:00")),
    ],
    "Anthony": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:30"), to_minutes("13:30")),
        (to_minutes("14:00"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
}

# Generate candidate start times at 30-minute granularity within work hours
candidate_starts = list(range(work_start, work_end - meeting_duration + 1, 30))

problem = Problem()
problem.addVariable("day", [day])
problem.addVariable("start", candidate_starts)

# Add constraints: meeting must not overlap any busy interval for each participant
def availability_constraint_factory(busy_intervals):
    def _constraint(start):
        start_time = start
        end_time = start + meeting_duration
        for b_start, b_end in busy_intervals:
            # Overlap if start < b_end and end > b_start
            if start_time < b_end and end_time > b_start:
                return False
        return True
    return _constraint

for person, busy in schedules.items():
    problem.addConstraint(availability_constraint_factory(busy), ("start",))

# Solve and pick earliest start
solutions = problem.getSolutions()
if not solutions:
    raise SystemExit("No feasible meeting time found.")

earliest = min(solutions, key=lambda s: s["start"])
start = earliest["start"]
end = start + meeting_duration

time_range = f"{{{minutes_to_str(start)}:{minutes_to_str(end)}}}"
print(time_range)
print(earliest["day"])