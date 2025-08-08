from datetime import datetime, timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def intersect(a, b):
    # Intersect interval a=[a0,a1) with b=[b0,b1)
    start = max(a[0], b[0])
    end = min(a[1], b[1])
    return (start, end) if start < end else None

def merge_intervals(intervals):
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

def complement_within(merged_busy, window):
    # Return free intervals within window by complementing merged_busy
    free = []
    ws, we = window
    cur = ws
    for s, e in merged_busy:
        if e <= ws or s >= we:
            continue
        s_clip, e_clip = max(s, ws), min(e, we)
        if cur < s_clip:
            free.append((cur, s_clip))
        cur = max(cur, e_clip)
    if cur < we:
        free.append((cur, we))
    return free

# Inputs
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy schedules
steven_busy = []
roy_busy = []
cynthia_busy = [("09:30","10:30"), ("11:30","12:00"), ("13:00","13:30"), ("15:00","16:00")]
lauren_busy = [("09:00","09:30"), ("10:30","11:00"), ("11:30","12:00"), ("13:00","13:30"), ("14:00","14:30"), ("15:00","15:30"), ("16:00","17:00")]
robert_busy = [("10:30","11:00"), ("11:30","12:00"), ("12:30","13:30"), ("14:00","16:00")]

# Convert to minute intervals
def as_minutes(intervals):
    return [(to_minutes(s), to_minutes(e)) for s, e in intervals]

all_busy = (
    as_minutes(steven_busy) +
    as_minutes(roy_busy) +
    as_minutes(cynthia_busy) +
    as_minutes(lauren_busy) +
    as_minutes(robert_busy)
)

# Clip busy intervals to work window and merge
window = (work_start, work_end)
clipped_busy = []
for s, e in all_busy:
    inter = intersect((s, e), window)
    if inter:
        clipped_busy.append(inter)

merged_busy = merge_intervals(clipped_busy)
common_free = complement_within(merged_busy, window)

# Find earliest slot of required duration
start_time = end_time = None
for s, e in common_free:
    if e - s >= meeting_duration:
        start_time = s
        end_time = s + meeting_duration
        break

if start_time is None:
    raise RuntimeError("No suitable time slot found")

start_str = to_hhmm(start_time)
end_str = to_hhmm(end_time)

print(f"{{{start_str}:{end_str}}}")
print(day)