# Meeting scheduler for Monday between 09:00 and 17:00 with 30-minute duration

def m(h, mi):  # minutes since midnight
    return h * 60 + mi

WORK_START = m(9, 0)
WORK_END = m(17, 0)
DURATION = 30
DAY = "Monday"

def merge(intervals):
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

def complement_within(day_start, day_end, busy):
    busy = merge([(max(day_start, s), min(day_end, e)) for s, e in busy if e > day_start and s < day_end])
    free = []
    cur = day_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
    return free

def intersect(a, b):
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

def hhmm(minutes):
    h = minutes // 60
    mi = minutes % 60
    return f"{h:02d}:{mi:02d}"

# Busy schedules (half-open intervals [start, end))
walter_busy = []
cynthia_busy = [
    (m(9, 0), m(9, 30)),
    (m(10, 0), m(10, 30)),
    (m(13, 30), m(14, 30)),
    (m(15, 0), m(16, 0)),
]
ann_busy = [
    (m(10, 0), m(11, 0)),
    (m(13, 0), m(13, 30)),
    (m(14, 0), m(15, 0)),
    (m(16, 0), m(16, 30)),
]
catherine_busy = [
    (m(9, 0), m(11, 30)),
    (m(12, 30), m(13, 30)),
    (m(14, 30), m(17, 0)),
]
kyle_busy = [
    (m(9, 0), m(9, 30)),
    (m(10, 0), m(11, 30)),
    (m(12, 0), m(12, 30)),
    (m(13, 0), m(14, 30)),
    (m(15, 0), m(16, 0)),
]

participants_busy = [walter_busy, cynthia_busy, ann_busy, catherine_busy, kyle_busy]
participants_free = [complement_within(WORK_START, WORK_END, b) for b in participants_busy]

# Intersect all free intervals
from functools import reduce
common_free = reduce(intersect, participants_free)

# Find the earliest slot of required duration
slot_start = slot_end = None
for s, e in common_free:
    if e - s >= DURATION:
        slot_start = s
        slot_end = s + DURATION
        break

if slot_start is None:
    raise SystemExit("No suitable slot found, but the problem statement guarantees a solution.")

print(f"{DAY} {hhmm(slot_start)}:{hhmm(slot_end)}")