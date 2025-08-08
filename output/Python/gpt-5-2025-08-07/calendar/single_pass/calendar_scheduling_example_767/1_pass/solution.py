def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

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

def clamp_and_merge(busy, work_start, work_end):
    clamped = []
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if s < e:
            clamped.append((s, e))
    return merge_intervals(clamped)

def free_from_busy(busy, work_start, work_end):
    busy = clamp_and_merge(busy, work_start, work_end)
    free = []
    cur = work_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
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

def find_meeting():
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # minutes
    days = ["Monday", "Tuesday", "Wednesday"]

    martha_busy_raw = {
        "Monday":    [("16:00", "17:00")],
        "Tuesday":   [("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("14:00", "14:30")],
    }
    beverly_busy_raw = {
        "Monday":    [("09:00", "13:30"), ("14:00", "17:00")],
        "Tuesday":   [("09:00", "17:00")],
        "Wednesday": [("09:30", "15:30"), ("16:30", "17:00")],
    }

    # Convert to minutes
    def convert(d):
        return {day: [(to_minutes(s), to_minutes(e)) for s, e in ivs] for day, ivs in d.items()}

    martha_busy = convert(martha_busy_raw)
    beverly_busy = convert(beverly_busy_raw)

    for day in days:
        martha_free = free_from_busy(martha_busy.get(day, []), work_start, work_end)
        beverly_free = free_from_busy(beverly_busy.get(day, []), work_start, work_end)
        common = intersect_intervals(martha_free, beverly_free)
        for s, e in common:
            if e - s >= duration:
                start = s
                end = s + duration
                print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
                return

if __name__ == "__main__":
    find_meeting()