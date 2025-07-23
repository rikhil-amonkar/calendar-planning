def main():
    # Convert time to minutes from 9:00 (0 minutes) to 17:00 (480 minutes)
    work_start = 0
    work_end = 480
    meeting_duration = 60

    # Busy intervals for each participant (in minutes from 9:00)
    anthony_busy = [
        (30, 60),    # 9:30-10:00
        (180, 240),  # 12:00-13:00
        (420, 450)   # 16:00-16:30
    ]
    
    pamela_busy = [
        (30, 60),    # 9:30-10:00
        (450, 480)   # 16:30-17:00
    ]
    # Add Pamela's constraint: unavailable after 14:30 (330 minutes from 9:00)
    pamela_busy.append((330, 480))
    
    zachary_busy = [
        (0, 150),    # 9:00-11:30
        (180, 210),  # 12:00-12:30
        (240, 270),  # 13:00-13:30
        (330, 360),  # 14:30-15:00
        (420, 480)   # 16:00-17:00
    ]
    
    # Combine all busy intervals
    all_busy = anthony_busy + pamela_busy + zachary_busy
    
    # Sort intervals by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free gaps of at least meeting_duration
    gaps = []
    prev_end = work_start
    for interval in merged:
        start, end = interval
        if start > prev_end:
            gap_length = start - prev_end
            if gap_length >= meeting_duration:
                gaps.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        gap_length = work_end - prev_end
        if gap_length >= meeting_duration:
            gaps.append((prev_end, work_end))
    
    # Choose the first suitable gap
    if gaps:
        gap_start, gap_end = gaps[0]
        meeting_start = gap_start
        meeting_end = gap_start + meeting_duration
        
        # Convert meeting times back to HH:MM format
        start_hour = 9 + meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = 9 + meeting_end // 60
        end_minute = meeting_end % 60
        
        # Format as HH:MM:HH:MM
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        
        # Output day and time string
        print("Monday")
        print(time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()