from datetime import datetime, timedelta

def to_minutes(t):
    return int(datetime.strptime(t, "%H:%M").hour) * 60 + int(datetime.strptime(t, "%H:%M").minute)

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    # Convert to minutes and sort
    ints = sorted([(to_minutes(s), to_minutes(e)) for s, e in intervals], key=lambda x: x[0])
    merged = [ints[0]]
    for s, e in ints[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def subtract_from_working_hours(work_start, work_end, busy_intervals):
    # busy_intervals are merged and in minutes
    free = []
    current = work_start
    for s, e in busy_intervals:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(a, b):
    # a, b are lists of (start_min, end_min) sorted and non-overlapping
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            result.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

def find_meeting_slot(common_free, duration_min):
    for s, e in common_free:
        if e - s >= duration_min:
            return s, s + duration_min
    return None

def main():
    day = "Monday"
    work_start_str, work_end_str = "09:00", "17:00"
    work_start = to_minutes(work_start_str)
    work_end = to_minutes(work_end_str)
    duration_min = 30

    schedules = {
        "Patrick": [("13:30", "14:00"), ("14:30", "15:00")],
        "Shirley": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:30", "15:00"), ("16:00", "17:00")],
        "Jeffrey": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "17:00")],
        "Gloria":  [("11:30", "12:00"), ("15:00", "15:30")],
        "Nathan":  [("09:00", "09:30"), ("10:30", "12:00"), ("14:00", "17:00")],
        "Angela":  [("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:00"), ("15:30", "16:30")],
        "David":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:00"), ("14:30", "16:30")],
    }

    # Compute each participant's free intervals within work hours
    all_free = []
    for person, busy in schedules.items():
        merged_busy = merge_intervals(busy)
        # Clip busy to work hours
        clipped_busy = []
        for s, e in merged_busy:
            s = max(s, work_start)
            e = min(e, work_end)
            if s < e:
                clipped_busy.append((s, e))
        person_free = subtract_from_working_hours(work_start, work_end, clipped_busy)
        all_free.append(person_free)

    # Intersect all free intervals
    common_free = [(work_start, work_end)]
    for free in all_free:
        common_free = intersect_intervals(common_free, free)
        if not common_free:
            break

    slot = find_meeting_slot(common_free, duration_min)
    if not slot:
        raise RuntimeError("No common slot found, but a solution was expected.")
    start_min, end_min = slot
    start_str, end_str = to_hhmm(start_min), to_hhmm(end_min)

    # Outputs required:
    # 1) HH:MM:HH:MM
    print(f"{start_str}:{end_str}")
    # 2) Day of the week
    print(day)
    # 3) Combined with braces as example format
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()