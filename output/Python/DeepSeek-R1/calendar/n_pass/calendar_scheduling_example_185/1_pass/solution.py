def main():
    # Convert time string to minutes from 9:00
    def time_to_min(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return (hours - 9) * 60 + minutes

    # Convert minutes back to time string
    def min_to_time(m):
        total_minutes = 9 * 60 + m
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Meeting parameters
    day = "Monday"
    duration_min = 30
    work_start = time_to_min("9:00")
    work_end = time_to_min("17:00")
    available_start = time_to_min("10:00")  # Megan's constraint
    available_end = work_end

    # Define busy intervals (each as [start, end) in minutes from 9:00)
    kimberly_busy = [
        (time_to_min("10:00"), time_to_min("10:30")),
        (time_to_min("11:00"), time_to_min("12:00")),
        (time_to_min("16:00"), time_to_min("16:30"))
    ]
    megan_busy = []  # No meetings, but constraint handled via available_start
    marie_busy = [
        (time_to_min("10:00"), time_to_min("11:00")),
        (time_to_min("11:30"), time_to_min("15:00")),
        (time_to_min("16:00"), time_to_min("16:30"))
    ]
    diana_busy = [
        (time_to_min("9:30"), time_to_min("10:00")),
        (time_to_min("10:30"), time_to_min("14:30")),
        (time_to_min("15:30"), time_to_min("17:00"))
    ]

    # Combine all busy intervals
    all_busy = kimberly_busy + megan_busy + marie_busy + diana_busy
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for s, e in all_busy[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free intervals within available hours
    free_intervals = []
    current = available_start
    for s, e in merged:
        if s > current:
            gap = s - current
            if gap >= duration_min:
                free_intervals.append((current, s))
            current = e
        else:
            if e > current:
                current = e
    if current < available_end:
        gap = available_end - current
        if gap >= duration_min:
            free_intervals.append((current, available_end))
    
    # Select the first available slot
    if free_intervals:
        start_min, _ = free_intervals[0]
        end_min = start_min + duration_min
        start_str = min_to_time(start_min)
        end_str = min_to_time(end_min)
        time_range_str = f"{start_str}:{end_str}"
        print(day)
        print(time_range_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()