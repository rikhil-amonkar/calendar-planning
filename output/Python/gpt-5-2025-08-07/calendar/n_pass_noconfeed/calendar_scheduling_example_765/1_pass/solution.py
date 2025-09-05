from datetime import timedelta

# Meeting parameters
MEETING_DURATION_MIN = 30
WORK_START = "09:00"
WORK_END = "17:00"
ALLOWED_DAYS = ["Monday", "Tuesday", "Wednesday"]

# Participants' busy schedules (inclusive of given constraints)
# Times are in HH:MM 24-hour format
busy = {
    "Joshua": {
        "Monday":   [("15:00", "15:30")],
        "Tuesday":  [("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00")],
        "Wednesday": []
    },
    "Joyce": {
        "Monday":   [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"),
                     ("13:00", "15:00"), ("15:30", "17:00")],
        "Tuesday":  [("09:00", "17:00")],
        "Wednesday":[("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:30"), ("16:00", "16:30")]
    }
}

# Preference: Joyce would rather not meet on Monday before 12:00
def preference_penalty(day: str, start_minutes: int) -> int:
    noon = 12 * 60
    if day == "Monday" and start_minutes < noon:
        return 1
    return 0

# Utilities
def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals = sorted((to_minutes(s), to_minutes(e)) for s, e in intervals)
    merged = []
    cur_s, cur_e = intervals[0]
    for s, e in intervals[1:]:
        if s <= cur_e:
            cur_e = max(cur_e, e)
        else:
            merged.append((cur_s, cur_e))
            cur_s, cur_e = s, e
    merged.append((cur_s, cur_e))
    return merged

def invert_intervals(busy_intervals, work_start, work_end):
    free = []
    cursor = work_start
    for s, e in busy_intervals:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_end:
        free.append((cursor, work_end))
    return free

def intersect_two(a, b):
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

def find_common_free(day):
    ws, we = to_minutes(WORK_START), to_minutes(WORK_END)
    all_free = None
    for person in busy:
        merged_busy = merge_intervals(busy[person].get(day, []))
        free = invert_intervals(merged_busy, ws, we)
        if all_free is None:
            all_free = free
        else:
            all_free = intersect_two(all_free, free)
        if not all_free:
            break
    return all_free or []

def candidate_slots(free_intervals, duration_min):
    for s, e in free_intervals:
        if e - s >= duration_min:
            yield (s, s + duration_min)

# Search respecting preferences, then earliest-by-time
best = None  # (penalty, day_index, start, end, day_name)
for day_idx, day in enumerate(ALLOWED_DAYS):
    common_free = find_common_free(day)
    for s, e in candidate_slots(common_free, MEETING_DURATION_MIN):
        pen = preference_penalty(day, s)
        candidate = (pen, day_idx, s, e, day)
        if best is None or candidate < best:
            best = candidate

if not best:
    raise SystemExit("No feasible slot found (but the problem statement guarantees one exists).")

_, _, start, end, chosen_day = best
print(f"{chosen_day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")