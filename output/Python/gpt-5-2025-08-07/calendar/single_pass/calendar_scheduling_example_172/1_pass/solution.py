from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
    out = []
    while i < len(a) and j < len(b):
        start = max(a[i][0], b[j][0])
        end = min(a[i][1], b[j][1])
        if start < end:
            out.append((start, end))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def invert_within_window(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    free = []
    current = ws
    for s, e in sorted(busy):
        if e <= ws or s >= we:
            continue
        s = max(s, ws)
        e = min(e, we)
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < we:
        free.append((current, we))
    return free

# Inputs
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

participants_busy = {
    "Patrick": [("09:00","09:30"), ("10:00","10:30"), ("13:30","14:00"), ("16:00","16:30")],
    "Kayla":   [("12:30","13:30"), ("15:00","15:30"), ("16:00","16:30")],
    "Carl":    [("10:30","11:00"), ("12:00","12:30"), ("13:00","13:30"), ("14:30","17:00")],
    "Christian":[("09:00","12:30"), ("13:00","14:00"), ("14:30","17:00")],
}

# Convert busy times to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in slots]
    for person, slots in participants_busy.items()
}

# Compute free intervals for each participant within working hours
free_by_person = {
    person: invert_within_window(busy, work_window)
    for person, busy in busy_minutes.items()
}

# Intersect all participants' free intervals
common_free = [(work_window[0], work_window[1])]
for person in free_by_person:
    common_free = intersect_intervals(common_free, free_by_person[person])

# Find earliest slot that fits duration
proposed_start, proposed_end = None, None
for s, e in common_free:
    if e - s >= duration:
        proposed_start, proposed_end = s, s + duration
        break

# Output
if proposed_start is not None:
    print(f"{day} {{{to_hhmm(proposed_start)}:{to_hhmm(proposed_end)}}}")
else:
    # Fallback (should not happen per problem statement)
    print(f"{day} {{No available slot}}")