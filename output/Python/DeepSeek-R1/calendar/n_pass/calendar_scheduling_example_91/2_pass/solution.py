def main():
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0    # 9:00 in minutes from reference
    work_end = 480    # 17:00 in minutes from reference
    meeting_duration = 60  # minutes

    # Define busy intervals in minutes (relative to 9:00) as (start, end) where end is exclusive
    danielle_busy = [
        (0, 60),    # 9:00-10:00
        (90, 120),   # 10:30-11:00
        (330, 360),  # 14:30-15:00
        (390, 420),  # 15:30-16:00
        (450, 480)   # 16:30-17:00
    ]
    
    bruce_busy = [
        (120, 150),  # 11:00-11:30
        (210, 240),  # 12:30-13:00
        (300, 330),  # 14:00-14:30
        (390, 420)   # 15:30-16:00
    ]
    
    eric_busy = [
        (0, 30),     # 9:00-9:30
        (60, 120),   # 10:00-11:00
        (150, 240),  # 11:30-13:00
        (330, 390)   # 14:30-15:30
    ]
    
    # Combine all busy intervals
    all_busy = danielle_busy + bruce_busy + eric_busy
    
    # Sort by start time
    all_busy_sorted = sorted(all_busy, key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged = []
    if all_busy_sorted:
        current_start, current_end = all_busy_sorted[0]
        for i in range(1, len(all_busy_sorted)):
            s, e = all_busy_sorted[i]
            if s <= current_end:  # Overlapping or adjacent
                if e > current_end:
                    current_end = e
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free intervals within work hours
    free_intervals = []
    # Check before first busy interval
    if merged and merged[0][0] > work_start:
        free_intervals.append((work_start, merged[0][0]))
    
    # Check between busy intervals
    for i in range(len(merged) - 1):
        current_end = merged[i][1]
        next_start = merged[i+1][0]
        if next_start > current_end:
            free_intervals.append((current_end, next_start))
    
    # Check after last busy interval
    if merged and merged[-1][1] < work_end:
        free_intervals.append((merged[-1][1], work_end))
    
    # If there are no busy intervals, the whole day is free
    if not merged:
        free_intervals.append((work_start, work_end))
    
    # Find the first free interval that can fit the meeting
    meeting_start_minutes = None
    for start, end in free_intervals:
        duration = end - start
        if duration >= meeting_duration:
            meeting_start_minutes = start
            break
    
    # Convert meeting start from minutes to time string
    if meeting_start_minutes is not None:
        total_minutes_start = meeting_start_minutes
        start_hour = 9 + total_minutes_start // 60
        start_minute = total_minutes_start % 60
        total_minutes_end = total_minutes_start + meeting_duration
        end_hour = 9 + total_minutes_end // 60
        end_minute = total_minutes_end % 60
        
        # Format as HH:MM for start and end
        time_str = f"{start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}"
        print(time_str)
        print("Monday")
    else:
        # According to the problem, there is a solution, so this should not happen
        print("No suitable time found")

if __name__ == "__main__":
    main()