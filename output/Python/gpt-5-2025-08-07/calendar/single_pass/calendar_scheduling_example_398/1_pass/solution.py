# Meeting Scheduler for Monday
# Finds a 30-minute slot between 09:00 and 17:00 that works for all participants.

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
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def find_meeting_slot(busy_intervals, work_start, work_end, duration):
    # Clamp busy intervals to working hours and merge
    clamped = []
    for s, e in busy_intervals:
        if e <= work_start or s >= work_end:
            continue
        clamped.append((max(s, work_start), min(e, work_end)))
    merged_busy = merge_intervals(clamped)

    # Find free intervals (complement within working hours)
    free_intervals = []
    prev_end = work_start
    for s, e in merged_busy:
        if s > prev_end:
            free_intervals.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))

    # Find earliest slot with required duration
    for s, e in free_intervals:
        if e - s >= duration:
            return s, s + duration
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules
    busy = []
    # Doris: 9:00-11:00, 13:30-14:00, 16:00-16:30
    busy += [(to_minutes("09:00"), to_minutes("11:00")),
             (to_minutes("13:30"), to_minutes("14:00")),
             (to_minutes("16:00"), to_minutes("16:30"))]
    # Theresa: 10:00-12:00
    busy += [(to_minutes("10:00"), to_minutes("12:00"))]
    # Christian: no meetings
    # Terry: 9:30-10:00, 11:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-17:00
    busy += [(to_minutes("09:30"), to_minutes("10:00")),
             (to_minutes("11:30"), to_minutes("12:00")),
             (to_minutes("12:30"), to_minutes("13:00")),
             (to_minutes("13:30"), to_minutes("14:00")),
             (to_minutes("14:30"), to_minutes("15:00")),
             (to_minutes("15:30"), to_minutes("17:00"))]
    # Carolyn: 9:00-10:30, 11:00-11:30, 12:00-13:00, 13:30-14:30, 15:00-17:00
    busy += [(to_minutes("09:00"), to_minutes("10:30")),
             (to_minutes("11:00"), to_minutes("11:30")),
             (to_minutes("12:00"), to_minutes("13:00")),
             (to_minutes("13:30"), to_minutes("14:30")),
             (to_minutes("15:00"), to_minutes("17:00"))]
    # Kyle: 9:00-9:30, 11:30-12:00, 12:30-13:00, 14:30-17:00
    busy += [(to_minutes("09:00"), to_minutes("09:30")),
             (to_minutes("11:30"), to_minutes("12:00")),
             (to_minutes("12:30"), to_minutes("13:00")),
             (to_minutes("14:30"), to_minutes("17:00"))]

    slot = find_meeting_slot(busy, work_start, work_end, duration)
    if not slot:
        raise RuntimeError("No suitable slot found, but a solution was expected.")

    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()