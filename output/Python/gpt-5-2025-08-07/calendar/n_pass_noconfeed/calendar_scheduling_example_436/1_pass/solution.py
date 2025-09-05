from datetime import datetime, timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def invert_within_window(busy, window_start, window_end):
    free = []
    current = window_start
    for s, e in busy:
        if e <= window_start or s >= window_end:
            continue
        s_clamped = max(s, window_start)
        e_clamped = min(e, window_end)
        if current < s_clamped:
            free.append((current, s_clamped))
        current = max(current, e_clamped)
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(a, b):
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

def find_slot(common_free, duration):
    for s, e in common_free:
        if e - s >= duration:
            return s, s + duration
    return None

day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

participants_busy = {
    "Patrick": [("13:30", "14:00"), ("14:30", "15:00")],
    "Shirley": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:30", "15:00"), ("16:00", "17:00")],
    "Jeffrey": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "17:00")],
    "Gloria": [("11:30", "12:00"), ("15:00", "15:30")],
    "Nathan": [("09:00", "09:30"), ("10:30", "12:00"), ("14:00", "17:00")],
    "Angela": [("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:00"), ("15:30", "16:30")],
    "David": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:00"), ("14:30", "16:30")],
}

# Convert to minutes and process each participant
all_free = None
for name, slots in participants_busy.items():
    busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in slots]
    busy_minutes = merge_intervals(busy_minutes)
    free_minutes = invert_within_window(busy_minutes, work_start, work_end)
    if all_free is None:
        all_free = free_minutes
    else:
        all_free = intersect_intervals(all_free, free_minutes)

slot = find_slot(all_free, meeting_duration)
if slot:
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])
    print(f"{start_str}:{end_str}")
    print(day)
else:
    print("No available slot found within constraints.")
    print(day)