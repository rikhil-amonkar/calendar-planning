def time_to_minutes(t):
    """Convert HH:MM to minutes since midnight."""
    hh, mm = map(int, t.split(':'))
    return hh * 60 + mm

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM."""
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

def find_free_slot(busy_intervals, day_start_min, day_end_min, duration_min):
    """Find first free slot of given duration within work hours."""
    # Add boundaries as busy blocks to simplify gap checking
    busy_with_boundaries = busy_intervals + [(day_end_min, day_end_min)]
    merged_busy = merge_intervals(busy_with_boundaries)
    
    # Start from day_start_min
    current_time = day_start_min
    for start_busy, end_busy in merged_busy:
        if start_busy - current_time >= duration_min:
            return (current_time, current_time + duration_min)
        if end_busy > current_time:
            current_time = end_busy
    return None

def main():
    # Work hours
    work_start = "9:00"
    work_end = "17:00"
    day_start_min = time_to_minutes(work_start)
    day_end_min = time_to_minutes(work_end)
    
    # Duration
    duration_min = 30
    
    # Busy schedules for Monday
    schedules = {
        "Jacob": ["13:30-14:00", "14:30-15:00"],
        "Diana": ["9:30-10:00", "11:30-12:00", "13:00-13:30", "16:00-16:30"],
        "Adam": ["9:30-10:30", "11:00-12:30", "15:30-16:00"],
        "Angela": ["9:30-10:00", "10:30-12:00", "13:00-15:30", "16:00-16:30"],
        "Dennis": ["9:00-9:30", "10:30-11:30", "13:00-15:00", "16:30-17:00"]
    }
    
    # Collect all busy intervals
    all_busy = []
    for person, blocks in schedules.items():
        for block in blocks:
            start_str, end_str = block.split('-')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            all_busy.append((start_min, end_min))
    
    # Merge intervals
    merged_busy = merge_intervals(all_busy)
    
    # Find free slot
    slot = find_free_slot(merged_busy, day_start_min, day_end_min, duration_min)
    
    if slot:
        start_slot, end_slot = slot
        start_time = minutes_to_time(start_slot)
        end_time = minutes_to_time(end_slot)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()