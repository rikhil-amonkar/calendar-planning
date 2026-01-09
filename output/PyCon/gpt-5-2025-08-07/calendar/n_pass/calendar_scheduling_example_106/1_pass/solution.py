from constraint import Problem

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting parameters
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 60  # minutes

# Participants' blocked times on Monday (inclusive start, exclusive end)
blocked = {
    "Olivia": [
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
    "Anna": [
        # No meetings
    ],
    "Virginia": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
    "Paul": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
}

# Generate possible start times at 30-minute increments within work hours
domain = []
latest_start = work_end - duration
t = work_start
while t <= latest_start:
    domain.append(t)
    t += 30  # 30-minute granularity

def no_overlap_with_blocks(start):
    end = start + duration
    # Check the meeting does not overlap any participant's blocked intervals
    for person, blocks in blocked.items():
        for b_start, b_end in blocks:
            # Allow touching edges but no overlap
            if not (end <= b_start or start >= b_end):
                return False
    return True

# Set up constraint problem
problem = Problem()
problem.addVariable("start", domain)
problem.addConstraint(no_overlap_with_blocks, ["start"])

solutions = problem.getSolutions()
if not solutions:
    raise SystemExit("No feasible time found.")

# Choose the earliest feasible start time
best_start = min(sol["start"] for sol in solutions)
best_end = best_start + duration

# Output in the required format: Day {HH:MM:HH:MM}
print(f"{day} {{{minutes_to_time(best_start)}:{minutes_to_time(best_end)}}}")