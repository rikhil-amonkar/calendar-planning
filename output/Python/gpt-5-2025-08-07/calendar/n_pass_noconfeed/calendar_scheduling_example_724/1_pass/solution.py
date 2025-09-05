from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_intervals(base: List[Tuple[int, int]], sub: Tuple[int, int]) -> List[Tuple[int, int]]:
    """Subtract a single interval 'sub' from a list of non-overlapping sorted 'base' intervals."""
    res = []
    s, e = sub
    for bs, be in base:
        if e <= bs or s >= be:
            # No overlap
            res.append((bs, be))
        else:
            # Overlap cases
            if s > bs:
                res.append((bs, s))
            if e < be:
                res.append((e, be))
    return res

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    """Intersect two lists of non-overlapping sorted intervals."""
    i = j = 0
    res = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            res.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return res

def canonical(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    """Merge overlapping intervals; assumes intervals may be unsorted."""
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

# Inputs
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes
days_order = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules per participant
busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Tyler": {
        "Monday": [],
        "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                    (to_minutes("14:30"), to_minutes("15:00"))],
        "Wednesday": [(to_minutes("10:30"), to_minutes("11:00")),
                      (to_minutes("12:30"), to_minutes("13:00")),
                      (to_minutes("13:30"), to_minutes("14:00")),
                      (to_minutes("16:30"), to_minutes("17:00"))],
    },
    "Ruth": {
        "Monday": [(to_minutes("09:00"), to_minutes("10:00")),
                   (to_minutes("10:30"), to_minutes("12:00")),
                   (to_minutes("12:30"), to_minutes("14:30")),
                   (to_minutes("15:00"), to_minutes("16:00")),
                   (to_minutes("16:30"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("17:00"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("17:00"))],
    },
}

participants = list(busy.keys())

# Compute free intervals per participant per day
def free_intervals(person: str, day: str) -> List[Tuple[int, int]]:
    intervals = [(work_start, work_end)]
    for b in sorted(busy[person].get(day, [])):
        intervals = subtract_intervals(intervals, b)
        if not intervals:
            break
    return intervals

# Find common availability across all participants
common_free: Dict[str, List[Tuple[int, int]]] = {}
for day in days_order:
    # Start with first participant's free intervals
    if not participants:
        common_free[day] = []
        continue
    cf = free_intervals(participants[0], day)
    for person in participants[1:]:
        cf = intersect_two(cf, free_intervals(person, day))
        if not cf:
            break
    common_free[day] = cf

# Generate candidate slots of required duration
candidates: List[Tuple[int, str, Tuple[int, int]]] = []  # (score, day, (start, end))
for day in days_order:
    for s, e in common_free[day]:
        start = s
        while start + meeting_duration <= e:
            end = start + meeting_duration
            # Preference: Tyler would like to avoid Monday before 16:00
            penalty = 1 if (day == "Monday" and start < to_minutes("16:00")) else 0
            # Secondary sort keys: day order index, start time
            score = (penalty, days_order.index(day), start)
            candidates.append((score, day, (start, end)))
            # Move to next natural slot boundary (assume 30-min increments)
            start += 30

# Choose the best candidate based on score
if not candidates:
    raise RuntimeError("No available meeting slot found, despite problem statement guaranteeing one.")
best = min(candidates, key=lambda x: x[0])
_, day, (start, end) = best

# Output: Day of the week on one line, and time range in {HH:MM:HH:MM} on the next line
print(day)
print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")