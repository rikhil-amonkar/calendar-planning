def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    hh, mm = map(int, t.split(':'))
    return hh * 60 + mm

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM'."""
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

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

def find_free_slot(busy_intervals, work_start, work_end, duration):
    """Find first free slot of given duration within work hours."""
    # Merge all busy intervals
    merged_busy = merge_intervals(busy_intervals)
    
    # Find free intervals
    free_intervals = []
    current_start = work_start
    
    for start, end in merged_busy:
        if start > current_start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    
    # Find first free interval long enough
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # Work hours
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes
    
    # Blocked times for each person (in minutes since midnight)
    diane = [
        ("9:30", "10:00"),
        ("14:30", "15:00")
    ]
    jack = [
        ("13:30", "14:00"),
        ("14:30", "15:00")
    ]
    eugene = [
        ("9:00", "10:00"),
        ("10:30", "11:30"),
        ("12:00", "14:30"),
        ("15:00", "16:30")
    ]
    patricia = [
        ("9:30", "10:30"),
        ("11:00", "12:00"),
        ("12:30", "14:00"),
        ("15:00", "16:30")
    ]
    
    # Combine all busy intervals
    all_busy = []
    for person in [diane, jack, eugene, patricia]:
        for start_str, end_str in person:
            all_busy.append((time_to_minutes(start_str), time_to_minutes(end_str)))
    
    # Find free slot
    slot = find_free_slot(all_busy, work_start, work_end, duration)
    
    if slot:
        start_min, end_min = slot
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()