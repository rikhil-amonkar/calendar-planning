from datetime import datetime

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_within_work(busy, work_start, work_end):
    busy = merge_intervals([(max(s, work_start), min(e, work_end)) for s, e in busy if e > work_start and s < work_end])
    free = []
    cur = work_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect_two(a, b):
    i, j = 0, 0
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

def intersect_all(lists):
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

def find_meeting_slot(free_intersections, duration, prefer_before=None):
    # prefer_before is a minute threshold; prefer slots that start <= prefer_before
    candidates = []
    for s, e in free_intersections:
        if e - s >= duration:
            candidates.append((s, s + duration))
    if not candidates:
        return None
    if prefer_before is not None:
        preferred = [c for c in candidates if c[0] <= prefer_before]
        if preferred:
            return preferred[0]
    return candidates[0]

# Problem setup
day = "Monday"
work_start_str, work_end_str = "09:00", "17:00"
duration_min = 30

jack_busy_str = [("09:30","10:30"), ("11:00","11:30"), ("12:30","13:00"), ("14:00","14:30"), ("16:00","16:30")]
charlotte_busy_str = [("09:30","10:00"), ("10:30","12:00"), ("12:30","13:30"), ("14:00","16:00")]

work_start = to_minutes(work_start_str)
work_end = to_minutes(work_end_str)

jack_busy = [(to_minutes(s), to_minutes(e)) for s, e in jack_busy_str]
charlotte_busy = [(to_minutes(s), to_minutes(e)) for s, e in charlotte_busy_str]

jack_free = invert_within_work(jack_busy, work_start, work_end)
charlotte_free = invert_within_work(charlotte_busy, work_start, work_end)

common_free = intersect_all([jack_free, charlotte_free])

# Preference: Jack would like to avoid meetings after 12:30
prefer_before = to_minutes("12:30")

slot = find_meeting_slot(common_free, duration_min, prefer_before=prefer_before)

if slot is None:
    raise ValueError("No feasible meeting slot found, but the task guarantees a solution.")

start_str = to_hhmm(slot[0])
end_str = to_hhmm(slot[1])

print(day)
print(f"{start_str}:{end_str}")