from functools import reduce

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
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def clip_interval(interval, window):
    s, e = interval
    ws, we = window
    s = max(s, ws)
    e = min(e, we)
    if s < e:
        return (s, e)
    return None

def complement_within(busy, window):
    ws, we = window
    if not busy:
        return [(ws, we)]
    free = []
    curr = ws
    for s, e in busy:
        if e <= curr:
            continue
        if s > curr:
            free.append((curr, s))
        curr = max(curr, e)
        if curr >= we:
            break
    if curr < we:
        free.append((curr, we))
    return free

def intersect_intervals(a, b):
    i = j = 0
    res = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        s = max(s1, s2)
        e = min(e1, e2)
        if s < e:
            res.append((s, e))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return res

def find_meeting(common_free, duration):
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_window = (to_minutes("09:00"), to_minutes("17:00"))
    duration = 60  # minutes

    schedules = {
        "Stephanie": [("10:00", "10:30"), ("16:00", "16:30")],
        "Cheryl":    [("10:00", "10:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:30", "17:00")],
        "Bradley":   [("09:30", "10:00"), ("10:30", "11:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
        "Steven":    [("09:00", "12:00"), ("13:00", "13:30"), ("14:30", "17:00")],
    }

    # Convert to minutes, clip within work window, merge, then find free intervals
    all_free = []
    for person, busy in schedules.items():
        busy_minutes = []
        for s, e in busy:
            interval = clip_interval((to_minutes(s), to_minutes(e)), work_window)
            if interval:
                busy_minutes.append(interval)
        busy_merged = merge_intervals(busy_minutes)
        free = complement_within(busy_merged, work_window)
        all_free.append(free)

    # Intersect all free intervals
    common_free = reduce(intersect_intervals, all_free)

    # Find earliest meeting slot
    meeting = find_meeting(common_free, duration)
    if meeting:
        start, end = meeting
        time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
        print(day)
        print("{" + time_range + "}")
    else:
        print(day)
        print("{No available slot}")

if __name__ == "__main__":
    main()