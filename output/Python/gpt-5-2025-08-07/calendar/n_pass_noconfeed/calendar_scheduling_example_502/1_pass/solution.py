from datetime import datetime, timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_busy_to_free(busy, work_start, work_end):
    busy = sorted(busy)
    free = []
    cur = work_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect_intervals(intervals_list):
    # intervals_list: list of lists of (start, end)
    if not intervals_list:
        return []
    result = intervals_list[0][:]
    for intervals in intervals_list[1:]:
        temp = []
        i = j = 0
        while i < len(result) and j < len(intervals):
            s1, e1 = result[i]
            s2, e2 = intervals[j]
            s, e = max(s1, s2), min(e1, e2)
            if s < e:
                temp.append((s, e))
            if e1 < e2:
                i += 1
            else:
                j += 1
        result = temp
        if not result:
            break
    return result

def find_slot(free_intersections, duration, preferred_before=None):
    # preferred_before: minute-of-day; prefer slots starting strictly before this time
    preferred_candidates = []
    other_candidates = []
    for s, e in free_intersections:
        if e - s >= duration:
            start = s
            end = s + duration
            if preferred_before is not None and start < preferred_before:
                preferred_candidates.append((start, end))
            else:
                other_candidates.append((start, end))
    if preferred_candidates:
        return min(preferred_candidates)  # earliest
    if other_candidates:
        return min(other_candidates)
    return None

# Problem setup (Monday)
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

# Existing schedules
jack_busy = [
    ("09:30","10:30"),
    ("11:00","11:30"),
    ("12:30","13:00"),
    ("14:00","14:30"),
    ("16:00","16:30"),
]
charlotte_busy = [
    ("09:30","10:00"),
    ("10:30","12:00"),
    ("12:30","13:30"),
    ("14:00","16:00"),
]

# Convert to minutes
jack_busy_mins = [(to_minutes(s), to_minutes(e)) for s, e in jack_busy]
charlotte_busy_mins = [(to_minutes(s), to_minutes(e)) for s, e in charlotte_busy]

# Compute free intervals within work hours
jack_free = invert_busy_to_free(jack_busy_mins, work_start, work_end)
charlotte_free = invert_busy_to_free(charlotte_busy_mins, work_start, work_end)

# Intersect free slots
common_free = intersect_intervals([jack_free, charlotte_free])

# Preference: Jack would like to avoid more meetings on Monday after 12:30
preference_cutoff = to_minutes("12:30")  # prefer starts before 12:30

slot = find_slot(common_free, meeting_duration, preferred_before=preference_cutoff)

if not slot:
    # Fallback (shouldn't happen given the prompt guarantees a solution)
    raise RuntimeError("No available slot found.")
start, end = slot

# Output
print(day)
print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")