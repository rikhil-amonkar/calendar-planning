def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    work_start = 0
    work_end = 480
    duration = 30  # 0.5 hours

    # Busy intervals for each participant in minutes (relative to 9:00) as [start, end)
    patrick = [(0, 30), (60, 90), (270, 300), (420, 450)]
    kayla = [(210, 270), (360, 390), (420, 450)]
    carl = [(90, 120), (180, 210), (240, 270), (330, 480)]
    christian = [(0, 210), (240, 300), (330, 480)]
    
    # Check possible meeting start times (every 30 minutes from work_start to work_end-duration)
    meeting_start = None
    for t in range(work_start, work_end - duration + 1, 30):
        meeting_end = t + duration
        # Check each participant's schedule
        available = True
        
        # Check Patrick
        for s, e in patrick:
            if t < e and meeting_end > s:
                available = False
                break
        if not available:
            continue
            
        # Check Kayla
        for s, e in kayla:
            if t < e and meeting_end > s:
                available = False
                break
        if not available:
            continue
            
        # Check Carl
        for s, e in carl:
            if t < e and meeting_end > s:
                available = False
                break
        if not available:
            continue
            
        # Check Christian
        for s, e in christian:
            if t < e and meeting_end > s:
                available = False
                break
        if not available:
            continue
            
        # All participants available at this time
        meeting_start = t
        break
    
    # Output result
    if meeting_start is not None:
        start_hour = 9 + meeting_start // 60
        start_minute = meeting_start % 60
        print("Monday")
        print(f"{start_hour}:{start_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()