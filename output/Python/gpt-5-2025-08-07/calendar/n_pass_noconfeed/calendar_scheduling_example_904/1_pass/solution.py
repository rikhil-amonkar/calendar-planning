# Meeting scheduler for Daniel and Bradley
# Finds a 30-minute slot between 09:00 and 17:00 on weekdays,
# honoring hard constraints and preferring to avoid soft-avoid days.

from typing import List, Tuple, Dict

# Utilities
def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]  # [start, end) in minutes

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(intervals: List[Interval], window: Interval) -> List[Interval]:
    # intervals assumed merged and within window
    ws, we = window
    if not intervals:
        return [(ws, we)]
    free = []
    prev_end = ws
    for s, e in intervals:
        if s > prev_end:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < we:
        free.append((prev_end, we))
    return free

def intersect_two(a: List[Interval], b: List[Interval]) -> List[Interval]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def intersect_many(lists: List[List[Interval]]) -> List[Interval]:
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

# Data
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
WORK_START, WORK_END = to_minutes("09:00"), to_minutes("17:00")
WORK_WINDOW = (WORK_START, WORK_END)
MEETING_DURATION = 30  # minutes

participants = {
    "Daniel": {
        "busy": {
            "Monday":    [("09:30","10:30"), ("12:00","12:30"), ("13:00","14:00"), ("14:30","15:00"), ("15:30","16:00")],
            "Tuesday":   [("11:00","12:00"), ("13:00","13:30"), ("15:30","16:00"), ("16:30","17:00")],
            "Wednesday": [("09:00","10:00"), ("14:00","14:30")],
            "Thursday":  [("10:30","11:00"), ("12:00","13:00"), ("14:30","15:00"), ("15:30","16:00")],
            "Friday":    [("09:00","09:30"), ("11:30","12:00"), ("13:00","13:30"), ("16:30","17:00")],
        },
        "soft_avoid_days": {"Wednesday", "Thursday"},
        # No hard day/time restrictions beyond work hours
        "allowed_windows": {day: [WORK_WINDOW] for day in days},
    },
    "Bradley": {
        "busy": {
            "Monday":    [("09:30","11:00"), ("11:30","12:00"), ("12:30","13:00"), ("14:00","15:00")],
            "Tuesday":   [("10:30","11:00"), ("12:00","13:00"), ("13:30","14:00"), ("15:30","16:30")],
            "Wednesday": [("09:00","10:00"), ("11:00","13:00"), ("13:30","14:00"), ("14:30","17:00")],
            "Thursday":  [("09:00","12:30"), ("13:30","14:00"), ("14:30","15:00"), ("15:30","16:30")],
            "Friday":    [("09:00","09:30"), ("10:00","12:30"), ("13:00","13:30"), ("14:00","14:30"), ("15:30","16:30")],
        },
        "soft_avoid_days": set(),  # None stated
        # Hard constraints: Not Monday, not Friday; Tuesday not before 12:00
        "allowed_windows": {
            "Monday":    [],  # disallowed
            "Tuesday":   [(to_minutes("12:00"), WORK_END)],
            "Wednesday": [WORK_WINDOW],
            "Thursday":  [WORK_WINDOW],
            "Friday":    [],  # disallowed
        },
    }
}

# Prepare busy intervals in minutes and merged
def prepare_busy_minutes(busy_str: Dict[str, List[Tuple[str,str]]]) -> Dict[str, List[Interval]]:
    out = {}
    for d in days:
        intervals = [(to_minutes(s), to_minutes(e)) for s, e in busy_str.get(d, [])]
        out[d] = merge_intervals(intervals)
    return out

for p in participants.values():
    p["busy_minutes"] = prepare_busy_minutes(p["busy"])
    # Ensure allowed windows are merged and within work hours
    aw = {}
    for d in days:
        lst = p["allowed_windows"].get(d, [WORK_WINDOW])
        # clip to work hours
        clipped = []
        for s, e in lst:
            s = max(s, WORK_START)
            e = min(e, WORK_END)
            if s < e:
                clipped.append((s, e))
        aw[d] = merge_intervals(clipped)
    p["allowed_minutes"] = aw

# Determine day ordering: exclude any day with empty allowed window for any participant.
# Prioritize days with fewer soft-avoid counts.
candidate_days = []
for d in days:
    if all(participants[name]["allowed_minutes"][d] for name in participants):
        soft_count = sum(1 for name in participants if d in participants[name]["soft_avoid_days"])
        candidate_days.append((soft_count, d))

candidate_days.sort()  # by soft_count ascending then day order

def find_slot() -> Tuple[str, Interval]:
    for _, day in candidate_days:
        # Base allowed window = intersection of all participants' allowed windows
        allowed_lists = [participants[name]["allowed_minutes"][day] for name in participants]
        allowed = intersect_many(allowed_lists)
        if not allowed:
            continue

        # For each participant: free within work window, then restrict to allowed
        common_free_lists = []
        for name in participants:
            busy = participants[name]["busy_minutes"][day]
            free = invert_intervals(busy, WORK_WINDOW)
            free = intersect_two(free, allowed)
            common_free_lists.append(free)

        common = intersect_many(common_free_lists)
        for s, e in common:
            if e - s >= MEETING_DURATION:
                return day, (s, s + MEETING_DURATION)
    raise RuntimeError("No feasible slot found, but one was expected.")

day, (start, end) = find_slot()
print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")