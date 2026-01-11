def time_to_minutes(t):
    """Convert HH:MM to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM."""
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def find_meeting_slot(busy1, busy2, work_start, work_end, duration):
    """Find first free slot of given duration for two people."""
    # Combine busy intervals
    all_busy = busy1 + busy2
    merged_busy = merge_intervals(all_busy)
    
    # Find free slots within work hours
    free_slots = []
    current_time = work_start
    
    for start, end in merged_busy:
        if current_time < start:
            free_slots.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < work_end:
        free_slots.append((current_time, work_end))
    
    # Find first slot with enough duration
    for start, end in free_slots:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # Work hours 9:00 to 17:00
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    
    # Busy times in minutes since midnight
    kayla_busy = [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("14:30"), time_to_minutes("16:00"))
    ]
    
    rebecca_busy = [
        (time_to_minutes("9:00"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
    
    duration_minutes = 60  # 1 hour
    
    slot = find_meeting_slot(kayla_busy, rebecca_busy, work_start, work_end, duration_minutes)
    
    if slot:
        start, end = slot
        print(f"{minutes_to_time(start)}:{minutes_to_time(end)}")
        print("Monday")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()