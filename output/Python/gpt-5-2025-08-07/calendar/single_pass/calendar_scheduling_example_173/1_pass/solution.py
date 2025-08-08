from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def subtract_busy(work_window: Tuple[int, int], busies: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ws, we = work_window
    # Clip busies to the work window and merge overlaps
    clipped = []
    for s, e in busies:
        s = max(s, ws)
        e = min(e, we)
        if s < e:
            clipped.append((s, e))
    merged = merge_intervals(clipped)

    free = []
    cur = ws
    for s, e in merged:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
        if cur >= we:
            break
    if cur < we:
        free.append((cur, we))
    return free

def intersect_lists(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Problem setup
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

schedules_str = {
    "Jacqueline": [("09:00","09:30"),("11:00","11:30"),("12:30","13:00"),("15:30","16:00")],
    "Harold":     [("10:00","10:30"),("13:00","13:30"),("15:00","17:00")],
    "Arthur":     [("09:00","09:30"),("10:00","12:30"),("14:30","15:00"),("15:30","17:00")],
    "Kelly":      [("09:00","09:30"),("10:00","11:00"),("11:30","12:30"),("14:00","15:00"),("15:30","16:00")],
}

# Convert schedules to minutes
schedules = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in schedules_str.items()
}

# Compute free intervals per participant within work hours
work_window = (work_start, work_end)
free_by_person = {
    person: subtract_busy(work_window, busies)
    for person, busies in schedules.items()
}

# Intersect all participants' free intervals
common_free = None
for person, free_list in free_by_person.items():
    if common_free is None:
        common_free = free_list
    else:
        common_free = intersect_lists(common_free, free_list)

# Apply Harold's constraint: meeting should not go past 13:00 on Monday
harold_end_limit = to_minutes("13:00")

# Find earliest feasible slot
start_time = end_time = None
if common_free:
    for s, e in common_free:
        # Ensure meeting ends by Harold's limit and fits within the free block
        latest_allowed_end = min(e, harold_end_limit)
        if s + meeting_duration <= latest_allowed_end:
            start_time = s
            end_time = s + meeting_duration
            break

# Output
if start_time is None:
    raise RuntimeError("No feasible time found, but a solution was promised to exist.")

start_str = to_hhmm(start_time)
end_str = to_hhmm(end_time)

print(day)
print(f"{{{start_str}:{end_str}}}")