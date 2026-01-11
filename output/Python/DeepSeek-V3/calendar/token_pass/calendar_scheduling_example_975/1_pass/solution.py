def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def parse_schedule(schedule_str, day):
    """
    Parse schedule string for a given day.
    schedule_str format: 'day during HH:MM to HH:MM, ...'
    Returns list of (start_min, end_min) within that day.
    """
    intervals = []
    # Work hours in minutes from 9:00 (540) to 17:00 (1020)
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Split by commas and find entries for the given day
    parts = schedule_str.split(', ')
    for part in parts:
        if day in part:
            # Extract time part
            time_part = part.split(' during ')[1]
            start_str, end_str = time_part.split(' to ')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            # Clip to work hours
            if end_min <= work_start or start_min >= work_end:
                continue
            start_min = max(start_min, work_start)
            end_min = min(end_min, work_end)
            if start_min < end_min:
                intervals.append((start_min, end_min))
    return intervals

def merge_intervals(intervals):
    """Merge overlapping intervals."""
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
    """Find free slots given busy intervals."""
    free_slots = []
    last_end = work_start
    for start, end in busy_intervals:
        if start - last_end >= duration:
            free_slots.append((last_end, start))
        last_end = max(last_end, end)
    if work_end - last_end >= duration:
        free_slots.append((last_end, work_end))
    return free_slots

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    nicole_schedule = (
        "Tuesday during 16:00 to 16:30, "
        "Wednesday during 15:00 to 15:30, "
        "Friday during 12:00 to 12:30, 15:30 to 16:00"
    )
    daniel_schedule = (
        "Monday during 9:00 to 12:30, 13:00 to 13:30, 14:00 to 16:30, "
        "Tuesday during 9:00 to 10:30, 11:30 to 12:30, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00, "
        "Wednesday during 9:00 to 10:00, 11:00 to 12:30, 13:00 to 13:30, 14:00 to 14:30, 16:30 to 17:00, "
        "Thursday during 11:00 to 12:00, 13:00 to 14:00, 15:00 to 15:30, "
        "Friday during 10:00 to 11:00, 11:30 to 12:00, 12:30 to 14:30, 15:00 to 15:30, 16:00 to 16:30"
    )
    
    work_start_min = 9 * 60
    work_end_min = 17 * 60
    duration_min = 60
    
    for day in days:
        nicole_busy = parse_schedule(nicole_schedule, day)
        daniel_busy = parse_schedule(daniel_schedule, day)
        all_busy = merge_intervals(nicole_busy + daniel_busy)
        free_slots = find_free_slots(all_busy, work_start_min, work_end_min, duration_min)
        
        if free_slots:
            slot_start, slot_end = free_slots[0]
            # We need a 1-hour meeting starting at slot_start
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            print(f"{day}")
            print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            return

if __name__ == "__main__":
    main()