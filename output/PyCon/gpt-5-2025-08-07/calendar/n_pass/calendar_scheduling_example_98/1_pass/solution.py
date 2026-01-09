# Requires: python-constraint
from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Meeting parameters
day_of_week = "Monday"
meeting_duration = 30  # minutes
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")

# Participants' busy schedules (inclusive of start, exclusive of end)
juan_busy = [("09:00", "10:30"), ("15:30", "16:00")]
marilyn_busy = [("11:00", "11:30"), ("12:30", "13:00")]
ronald_busy = [("09:00", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")]

# Additional constraint: Juan cannot meet after 16:00 (meeting must end by 16:00)
juan_end_limit = to_minutes("16:00")

# Build domain of possible start times at 30-minute granularity within working hours
domain = []
t = work_start
while t + meeting_duration <= work_end:
    domain.append(t)
    t += 30  # step in 30-minute increments

problem = Problem()
problem.addVariable("start", domain)

def no_overlap(start, busy_start, busy_end):
    # No overlap if meeting ends on/before busy_start or starts on/after busy_end
    return (start + meeting_duration) <= busy_start or start >= busy_end

# Working hours and Juan's end-time constraint
problem.addConstraint(lambda s: s >= work_start and s + meeting_duration <= work_end and s + meeting_duration <= juan_end_limit, ["start"])

# Add busy constraints for each participant
for bs, be in juan_busy:
    bs_m, be_m = to_minutes(bs), to_minutes(be)
    problem.addConstraint(lambda s, bs=bs_m, be=be_m: no_overlap(s, bs, be), ["start"])

for bs, be in marilyn_busy:
    bs_m, be_m = to_minutes(bs), to_minutes(be)
    problem.addConstraint(lambda s, bs=bs_m, be=be_m: no_overlap(s, bs, be), ["start"])

for bs, be in ronald_busy:
    bs_m, be_m = to_minutes(bs), to_minutes(be)
    problem.addConstraint(lambda s, bs=bs_m, be=be_m: no_overlap(s, bs, be), ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found, though one was expected.")

# Choose the earliest valid start time
best_start = min(sol["start"] for sol in solutions)
best_end = best_start + meeting_duration

time_range = f"{{{to_hhmm(best_start)}:{to_hhmm(best_end)}}}"
print(time_range)
print(day_of_week)