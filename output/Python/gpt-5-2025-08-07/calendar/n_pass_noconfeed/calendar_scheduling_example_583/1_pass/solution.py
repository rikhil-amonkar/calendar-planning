def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

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

def invert_intervals(busy, day_start, day_end):
    free = []
    current = day_start
    for s, e in busy:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_intervals(a, b):
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

def earliest_slot(free_intervals, duration):
    for s, e in free_intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    lisa_busy = [
        ("09:00","09:30"),
        ("10:30","11:00"),
        ("14:00","16:00"),
    ]
    anthony_busy = [
        ("09:00","09:30"),
        ("11:00","11:30"),
        ("12:30","13:30"),
        ("14:00","15:00"),
        ("15:30","16:00"),
        ("16:30","17:00"),
    ]

    lisa_busy_m = merge_intervals([(to_minutes(s), to_minutes(e)) for s, e in lisa_busy])
    anthony_busy_m = merge_intervals([(to_minutes(s), to_minutes(e)) for s, e in anthony_busy])

    lisa_free = invert_intervals(lisa_busy_m, work_start, work_end)
    anthony_free = invert_intervals(anthony_busy_m, work_start, work_end)

    common_free = intersect_intervals(lisa_free, anthony_free)
    slot = earliest_slot(common_free, duration)

    if slot:
        start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])
        print(f"{day} {{{start_str}:{end_str}}}")
    else:
        print(f"{day} {{No available slot}}")

if __name__ == "__main__":
    main()