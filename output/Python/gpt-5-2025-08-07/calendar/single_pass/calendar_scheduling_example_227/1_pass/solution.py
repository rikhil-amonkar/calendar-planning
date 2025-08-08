# Meeting scheduler for the given participants and constraints

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a: Tuple[int, int], b: Tuple[int, int]) -> bool:
    # intervals [start, end)
    return not (a[1] <= b[0] or b[1] <= a[0])

# Settings
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules (Monday)
participants_busy = {
    "Natalie": [],
    "David": [
        ("11:30", "12:00"),
        ("14:30", "15:00"),
    ],
    "Douglas": [
        ("09:30", "10:00"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("14:30", "15:00"),
    ],
    "Ralph": [
        ("09:00", "09:30"),
        ("10:00", "11:00"),
        ("11:30", "12:30"),
        ("13:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00"),
    ],
    "Jordan": [
        ("09:00", "10:00"),
        ("12:00", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00"),
        ("15:30", "17:00"),
    ],
}

# Convert busy times to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in participants_busy.items()
}

# Additional constraint: David does not want to meet before 14:00
earliest_allowed = to_minutes("14:00")

# Find the earliest feasible slot
proposed = None
for start in range(max(work_start, earliest_allowed), work_end - duration + 1, 30):
    end = start + duration
    candidate = (start, end)
    feasible = True
    for person, intervals in busy_minutes.items():
        # Check within work hours
        if start < work_start or end > work_end:
            feasible = False
            break
        # Check busy overlaps
        if any(overlaps(candidate, b) for b in intervals):
            feasible = False
            break
    if feasible:
        proposed = candidate
        break

if not proposed:
    raise RuntimeError("No feasible meeting time found, despite problem guarantee.")

start_str = to_hhmm(proposed[0])
end_str = to_hhmm(proposed[1])

# Output must include both the time range in {HH:MM:HH:MM} and the day of the week
print(f"{{{start_str}:{end_str}}}")
print(day)