def time_to_minutes(t):
    """Convert HH:MM string to minutes since midnight."""
    hh, mm = map(int, t.split(':'))
    return hh * 60 + mm

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM string."""
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
    
    # Check before first busy interval
    if merged_busy:
        first_start = merged_busy[0][0]
        if work_start + duration <= first_start:
            return (work_start, work_start + duration)
        
        # Check between busy intervals
        for i in range(len(merged_busy) - 1):
            current_end = merged_busy[i][1]
            next_start = merged_busy[i + 1][0]
            if current_end + duration <= next_start:
                return (current_end, current_end + duration)
        
        # Check after last busy interval
        last_end = merged_busy[-1][1]
        if last_end + duration <= work_end:
            return (last_end, last_end + duration)
    else:
        # No busy intervals at all
        if work_start + duration <= work_end:
            return (work_start, work_start + duration)
    
    return None

def main():
    # Work hours
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 60  # minutes
    
    # Busy intervals for each person (in minutes since midnight)
    # Evelyn: free
    # Joshua
    joshua = [
        ("11:00", "12:30"),
        ("13:30", "14:30"),
        ("16:30", "17:00")
    ]
    # Kevin: free
    # Gerald: free
    # Jerry
    jerry = [
        ("9:00", "9:30"),
        ("10:30", "12:00"),
        ("12:30", "13:00"),
        ("13:30", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00")
    ]
    # Jesse
    jesse = [
        ("9:00", "9:30"),
        ("10:30", "12:00"),
        ("12:30", "13:00"),
        ("14:30", "15:00"),
        ("15:30", "16:30")
    ]
    # Kenneth
    kenneth = [
        ("10:30", "12:30"),
        ("13:30", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    
    # Combine all busy intervals
    all_busy = []
    for person in [joshua, jerry, jesse, kenneth]:
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