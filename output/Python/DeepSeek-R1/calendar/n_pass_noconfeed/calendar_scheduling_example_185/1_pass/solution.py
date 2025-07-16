def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes (from 9:00)
    work_start = 0
    work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes
    meeting_duration = 30  # minutes

    # Busy intervals for each participant in minutes (start, end)
    kimberly = [(60, 90), (120, 180), (420, 450)]
    megan = [(0, 60)]  # Avoid before 10:00, so busy from 9:00 to 10:00
    marie = [(60, 120), (150, 360), (420, 450)]
    diana = [(30, 60), (90, 330), (390, 480)]
    
    # Combine all busy intervals
    all_busy = kimberly + megan + marie + diana
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged_busy = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    else:
        merged_busy = []
    
    # Find free intervals
    free_intervals = []
    prev_end = work_start
    for start, end in merged_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    
    # Find the first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    if meeting_start is None:
        print("No suitable time found")
    else:
        # Convert meeting_start and meeting_end to time strings
        total_minutes_start = meeting_start
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        total_minutes_end = meeting_end
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        
        # Format as HH:MM
        start_str = f"{hours_start:02d}:{minutes_start:02d}"
        end_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the day and time in the required format
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()