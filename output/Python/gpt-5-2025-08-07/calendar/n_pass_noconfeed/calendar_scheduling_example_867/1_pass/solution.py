from datetime import timedelta

# Meeting configuration
WORK_START = 9 * 60   # minutes from midnight
WORK_END = 17 * 60    # minutes from midnight
MEETING_DURATION = 30 # minutes
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Busy schedules (start, end) in HH:MM (end-exclusive)
betty_busy = {
    "Monday":    [("10:00","10:30"), ("13:30","14:00"), ("15:00","15:30"), ("16:00","16:30")],
    "Tuesday":   [("9:00","9:30"), ("11:30","12:00"), ("12:30","13:00"), ("13:30","14:00"), ("16:30","17:00")],
    "Wednesday": [("9:30","10:30"), ("13:00","13:30"), ("14:00","14:30")],
    "Thursday":  [("9:30","10:00"), ("11:30","12:00"), ("14:00","14:30"), ("15:00","15:30"), ("16:30","17:00")],
}

scott_busy = {
    "Monday":    [("9:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
    "Tuesday":   [("9:00","9:30"), ("10:00","11:00"), ("11:30","12:00"), ("12:30","13:30"), ("14:00","15:00"), ("16:00","16:30")],
    "Wednesday": [("9:30","12:30"), ("13:00","13:30"), ("14:00","14:30"), ("15:00","15:30"), ("16:00","16:30")],
    "Thursday":  [("9:00","9:30"), ("10:00","10:30"), ("11:00","12:00"), ("12:30","13:00"), ("15:00","16:00"), ("16:30","17:00")],
}

# Constraints/Preferences:
# - Betty cannot meet on Monday and Tuesday.
# - Betty cannot meet on Thursday before 15:00.
# - Scott prefers to avoid Wednesday (use only if no other day works).
betty_day_block = {"Monday", "Tuesday"}
betty_time_block = {"Thursday": 15 * 60}  # earliest allowed start (in minutes) per day

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def overlaps(a_start, a_end, b_start, b_end) -> bool:
    return a_start < b_end and b_start < a_end

def free_slots(busy_list):
    # Return set of feasible 30-minute slot starts within work hours that do not overlap busy
    busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in busy_list]
    slots = []
    t = WORK_START
    while t + MEETING_DURATION <= WORK_END:
        conflict = any(overlaps(t, t + MEETING_DURATION, bs, be) for bs, be in busy_minutes)
        if not conflict:
            slots.append(t)
        t += MEETING_DURATION
    return set(slots)

# Compute availability per person per day
betty_free = {d: free_slots(betty_busy[d]) for d in DAYS}
scott_free = {d: free_slots(scott_busy[d]) for d in DAYS}

# Apply constraints
for d in DAYS:
    if d in betty_day_block:
        betty_free[d] = set()
    if d in betty_time_block:
        earliest = betty_time_block[d]
        betty_free[d] = {t for t in betty_free[d] if t >= earliest}

# Intersection of availability
candidate_slots = {d: sorted(betty_free[d].intersection(scott_free[d])) for d in DAYS}

# Selection respecting Scott's preference to avoid Wednesday if possible
# Priority order: Monday, Tuesday, Thursday, Wednesday (but Monday/Tuesday likely blocked by constraints)
day_priority = ["Monday", "Tuesday", "Thursday", "Wednesday"]

chosen_day = None
chosen_time = None

# First pass: prefer non-Wednesday
for d in day_priority:
    if d != "Wednesday" and candidate_slots[d]:
        chosen_day = d
        chosen_time = candidate_slots[d][0]
        break

# Second pass: allow Wednesday if nothing else works
if chosen_day is None and candidate_slots["Wednesday"]:
    chosen_day = "Wednesday"
    chosen_time = candidate_slots["Wednesday"][0]

def fmt(m):
    return f"{m//60:02d}:{m%60:02d}"

if chosen_day is None or chosen_time is None:
    raise RuntimeError("No feasible meeting slot found, but a solution was expected.")

start_str = fmt(chosen_time)
end_str = fmt(chosen_time + MEETING_DURATION)

# Output: Day and time range in braces, like: Thursday {16:00:16:30}
print(f"{chosen_day} {{{start_str}:{end_str}}}")