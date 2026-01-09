# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def hm_to_min(hm):
    h, m = map(int, hm.split(":"))
    return h * 60 + m

def min_to_hm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Meeting parameters
day_options = ["Monday"]
duration = 30  # minutes
work_start = hm_to_min("09:00")
work_end = hm_to_min("17:00")

# Participants' schedules (blocked times) for Monday, as [start, end) in minutes
evelyn_blocks = []  # no meetings the whole day
randy_blocks = [
    (hm_to_min("09:00"), hm_to_min("10:30")),
    (hm_to_min("11:00"), hm_to_min("15:30")),
    (hm_to_min("16:00"), hm_to_min("17:00")),
]

# Preferences
# Evelyn does not want to meet on Monday after 13:00
evelyn_latest_end_monday = hm_to_min("13:00")

# Candidate start times at 30-minute granularity within work hours
candidate_starts = list(range(work_start, work_end - duration + 1, 30))

problem = Problem()
problem.addVariable("day", day_options)
problem.addVariable("start", candidate_starts)

def no_overlap_with_blocks(start, blocks):
    meeting_end = start + duration
    for bs, be in blocks:
        # Overlap if start < be and meeting_end > bs
        if start < be and meeting_end > bs:
            return False
    return True

# Randy's calendar constraint
problem.addConstraint(lambda start: no_overlap_with_blocks(start, randy_blocks), ("start",))

# Evelyn's calendar constraint (no blocks, but run through for completeness)
problem.addConstraint(lambda start: no_overlap_with_blocks(start, evelyn_blocks), ("start",))

# Evelyn's preference: not after 13:00 on Monday
def evelyn_preference(day, start):
    if day == "Monday":
        return (start + duration) <= evelyn_latest_end_monday
    return True

problem.addConstraint(evelyn_preference, ("day", "start"))

# Ensure meeting within work hours (redundant given domain, but explicit)
problem.addConstraint(lambda start: work_start <= start and start + duration <= work_end, ("start",))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible start time
best = min(solutions, key=lambda s: (day_options.index(s["day"]), s["start"]))
start = best["start"]
end = start + duration
day = best["day"]

# Required outputs:
# 1) Time range in HH:MM:HH:MM format
# 2) Day of the week
# 3) Time range wrapped in braces like {HH:MM:HH:MM}
time_range = f"{min_to_hm(start)}:{min_to_hm(end)}"
print(time_range)
print(day)
print(f"{{{time_range}}}")