def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = intervals[0]
    for start, end in intervals[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    return merged

def find_free_slots(busy_intervals, work_start, work_end, duration):
    free_slots = []
    last_end = work_start
    for start, end in busy_intervals:
        if start > last_end and start - last_end >= duration:
            free_slots.append((last_end, start))
        last_end = max(last_end, end)
    if work_end - last_end >= duration:
        free_slots.append((last_end, work_end))
    return free_slots

def main():
    # Work hours
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes

    # Busy times for each person (Monday)
    michael_busy = [
        ("9:30", "10:30"),
        ("15:00", "15:30"),
        ("16:00", "16:30")
    ]
    arthur_busy = [
        ("9:00", "12:00"),
        ("13:00", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    eric_busy = []  # free all day

    # Combine all busy times
    all_busy = []
    for start, end in michael_busy + arthur_busy + eric_busy:
        all_busy.append((time_to_minutes(start), time_to_minutes(end)))

    # Merge intervals
    merged_busy = merge_intervals(all_busy)

    # Find free slots within work hours
    free_slots = find_free_slots(merged_busy, work_start, work_end, duration)

    # Output first suitable slot
    day = "Monday"
    if free_slots:
        slot_start, slot_end = free_slots[0]
        # We can start at slot_start for duration minutes
        meeting_start = slot_start
        meeting_end = meeting_start + duration
        print(f"{day}:{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()