from constraint import Problem

# Helper functions to work with time
def hm_to_min(hm):
    h, m = map(int, hm.split(":"))
    return h * 60 + m

def min_to_hm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return not (a_end <= b_start or b_end <= a_start)

# Problem setup
problem = Problem()

day = "Monday"
meeting_duration = 60  # minutes
work_start = hm_to_min("09:00")
work_end = hm_to_min("17:00")
step = 30  # minutes granularity

# Participants' busy intervals on Monday
busy = {
    "James": [
        (hm_to_min("11:30"), hm_to_min("12:00")),
        (hm_to_min("14:30"), hm_to_min("15:00")),
    ],
    "John": [
        (hm_to_min("09:30"), hm_to_min("11:00")),
        (hm_to_min("11:30"), hm_to_min("12:00")),
        (hm_to_min("12:30"), hm_to_min("13:30")),
        (hm_to_min("14:30"), hm_to_min("16:30")),
    ],
}

# Domain: all possible start times within work hours that can fit the meeting
domain = list(range(work_start, work_end - meeting_duration + 1, step))
problem.addVariable("start", domain)

# Constraint: meeting must not overlap with any participant's busy intervals and must fit in working hours
def is_valid(start):
    start_time = start
    end_time = start + meeting_duration
    if start_time < work_start or end_time > work_end:
        return False
    for intervals in busy.values():
        for b_start, b_end in intervals:
            if overlaps(start_time, end_time, b_start, b_end):
                return False
    return True

problem.addConstraint(is_valid, ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found, though one was expected.")

# Choose the earliest valid solution
best_start = min(solutions, key=lambda s: s["start"])["start"]
best_end = best_start + meeting_duration

start_str = min_to_hm(best_start)
end_str = min_to_hm(best_end)

# Required outputs:
# - The time range in braces like {HH:MM:HH:MM}
# - The day of the week
print(f"{{{start_str}:{end_str}}}")
print(day)