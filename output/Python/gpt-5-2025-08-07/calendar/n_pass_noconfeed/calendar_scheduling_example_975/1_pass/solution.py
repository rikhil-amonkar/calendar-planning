from datetime import timedelta

# Meeting parameters
work_start_str = "9:00"
work_end_str = "17:00"
meeting_duration_minutes = 60
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

WORK_START = to_minutes(work_start_str)
WORK_END = to_minutes(work_end_str)

# Participants' busy schedules
schedules = {
    "Nicole": {
        "Tuesday": [("16:00", "16:30")],
        "Wednesday": [("15:00", "15:30")],
        "Friday": [("12:00", "12:30"), ("15:30", "16:00")],
    },
    "Daniel": {
        "Monday": [("9:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],
        "Tuesday": [("9:00", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Wednesday": [("9:00", "10:00"), ("11:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],
        "Thursday": [("11:00", "12:00"), ("13:00", "14:00"), ("15:00", "15:30")],
        "Friday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    }
}

def merge_intervals(intervals):
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

def invert_to_free(busy, start, end):
    if not busy:
        return [(start, end)]
    free = []
    current = start
    for s, e in busy:
        s = max(s, start)
        e = min(e, end)
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < end:
        free.append((current, end))
    return free

def intersect(a, b):
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

# Normalize schedules: convert to minutes and merge overlaps per day per participant
busy_minutes = {}
for person, sched in schedules.items():
    busy_minutes[person] = {}
    for day in days:
        intervals = []
        for s, e in sched.get(day, []):
            intervals.append((to_minutes(s), to_minutes(e)))
        busy_minutes[person][day] = merge_intervals(intervals)

# Compute earliest common free slot
for day in days:
    # Start with each participant's free intervals on this day
    group_free = None
    for person in busy_minutes:
        person_busy = busy_minutes[person].get(day, [])
        person_free = invert_to_free(person_busy, WORK_START, WORK_END)
        if group_free is None:
            group_free = person_free
        else:
            group_free = intersect(group_free, person_free)
        if not group_free:
            break
    # Find earliest slot with required duration
    if group_free:
        for s, e in group_free:
            if e - s >= meeting_duration_minutes:
                start = s
                end = s + meeting_duration_minutes
                print(day)
                print(f"{{{to_str(start)}:{to_str(end)}}}")
                raise SystemExit

# If no slot found (should not happen per problem statement), print nothing or an error
print("No suitable time found.")