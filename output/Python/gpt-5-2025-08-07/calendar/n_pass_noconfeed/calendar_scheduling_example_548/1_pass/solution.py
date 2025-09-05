from typing import List, Tuple

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
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def complement_within(intervals: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    if ws >= we:
        return []
    # Clip busy intervals to the window and merge
    clipped = []
    for s, e in intervals:
        s = max(s, ws)
        e = min(e, we)
        if s < e:
            clipped.append((s, e))
    merged = merge_intervals(clipped)
    free = []
    cursor = ws
    for s, e in merged:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

def slots_of_duration(intervals: List[Tuple[int, int]], duration: int) -> List[Tuple[int, int]]:
    slots = []
    for s, e in intervals:
        if e - s >= duration:
            slots.append((s, s + duration))
    return slots

# Problem setup (Monday)
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
meeting_duration = 30  # minutes

# Participants' schedules (busy intervals)
judy_busy = []  # Judy is free the entire day
nicole_busy = [
    (to_minutes("09:00"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("16:30")),
]

# Preferences (soft): Nicole would rather not meet on Monday before 16:00
nicole_pref_not_before = to_minutes("16:00")

# Compute free intervals within work window
judy_free = complement_within(judy_busy, work_window)
nicole_free = complement_within(nicole_busy, work_window)

# Intersection of all participants' free intervals
common_free = intersect_intervals(judy_free, nicole_free)

# Candidate slots of desired duration
candidates = slots_of_duration(common_free, meeting_duration)

# Apply preference: pick earliest slot meeting Nicole's "not before 16:00"; else earliest overall
preferred = [slot for slot in candidates if slot[0] >= nicole_pref_not_before]
chosen = preferred[0] if preferred else (candidates[0] if candidates else None)

if not chosen:
    raise RuntimeError("No available slot found, but problem statement guarantees a solution.")

start_hhmm = to_hhmm(chosen[0])
end_hhmm = to_hhmm(chosen[1])

# Output
print(day)
print(f"{{{start_hhmm}:{end_hhmm}}}")