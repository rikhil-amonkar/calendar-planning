from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 60  # one hour

# Busy schedules
danielle_busy = [
    ("09:00", "10:00"),
    ("10:30", "11:00"),
    ("14:30", "15:00"),
    ("15:30", "16:00"),
    ("16:30", "17:00"),
]
bruce_busy = [
    ("11:00", "11:30"),
    ("12:30", "13:00"),
    ("14:00", "14:30"),
    ("15:30", "16:00"),
]
eric_busy = [
    ("09:00", "09:30"),
    ("10:00", "11:00"),
    ("11:30", "13:00"),
    ("14:30", "15:30"),
]

# Convert to minutes
def convert_busy(busy_list):
    return [(to_minutes(s), to_minutes(e)) for s, e in busy_list]

danielle_busy_m = convert_busy(danielle_busy)
bruce_busy_m = convert_busy(bruce_busy)
eric_busy_m = convert_busy(eric_busy)

# Candidate start times in 30-minute increments within work hours
candidate_starts = list(range(work_start, work_end - duration + 1, 30))
candidate_ends = [s + duration for s in candidate_starts]

# Setup CSP
problem = Problem()
problem.addVariable("start", candidate_starts)
problem.addVariable("end", candidate_ends)

# Meeting must last exactly 'duration' minutes
problem.addConstraint(lambda s, e: e - s == duration, ("start", "end"))

# Meeting must be within work hours
problem.addConstraint(lambda s, e: s >= work_start and e <= work_end, ("start", "end"))

# No overlap with any busy intervals (treat intervals as [start, end))
def no_overlap_with_interval(s, e, bs, be):
    # No overlap if meeting ends before busy starts OR starts after busy ends
    return e <= bs or s >= be

# Add constraints for each participant's busy times
for bs, be in danielle_busy_m:
    problem.addConstraint(lambda s, e, bs=bs, be=be: no_overlap_with_interval(s, e, bs, be), ("start", "end"))

for bs, be in bruce_busy_m:
    problem.addConstraint(lambda s, e, bs=bs, be=be: no_overlap_with_interval(s, e, bs, be), ("start", "end"))

for bs, be in eric_busy_m:
    problem.addConstraint(lambda s, e, bs=bs, be=be: no_overlap_with_interval(s, e, bs, be), ("start", "end"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible start time
best = min(solutions, key=lambda sol: sol["start"])
start_str = to_hhmm(best["start"])
end_str = to_hhmm(best["end"])
time_range = f"{start_str}:{end_str}"

# Output:
# - Time range in HH:MM:HH:MM
# - Day of week with the time range in braces, as requested
print(time_range)
print(f"{day} {{{time_range}}}")