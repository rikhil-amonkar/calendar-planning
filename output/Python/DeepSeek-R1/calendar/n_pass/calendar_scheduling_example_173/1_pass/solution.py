def main():
    # Work hours: 9:00 to 17:00, but Harold constraint: meeting must end by 13:00
    work_start_minutes = 0   # 9:00 in minutes from 9:00 (0 minutes)
    work_end_minutes = 240   # 13:00 (4 hours * 60 = 240 minutes)
    meeting_duration = 30    # 30 minutes

    # Convert busy times to minutes from 9:00 (only considering Monday and within 0-240 minutes)
    # Format: (start_minute, end_minute)
    jacqueline_busy = [
        (0, 30),    # 9:00-9:30
        (120, 150), # 11:00-11:30
        (210, 240)  # 12:30-13:00
    ]
    
    harold_busy = [
        (60, 90)    # 10:00-10:30
        # Note: 13:00-13:30 is at 240-270 -> beyond our window (240)
    ]
    
    arthur_busy = [
        (0, 30),    # 9:00-9:30
        (60, 210)   # 10:00-12:30
    ]
    
    kelly_busy = [
        (0, 30),    # 9:00-9:30
        (60, 120),  # 10:00-11:00
        (150, 210)  # 11:30-12:30
    ]
    
    # All participants' busy intervals in a list
    all_busy = [jacqueline_busy, harold_busy, arthur_busy, kelly_busy]
    
    # Iterate over possible start times from work_start_minutes to work_end_minutes - meeting_duration, in 30-min steps
    found_slot = None
    for start in range(work_start_minutes, work_end_minutes - meeting_duration + 1, 30):
        end = start + meeting_duration
        slot_ok = True
        
        # Check for each participant
        for participant_busy in all_busy:
            conflict = False
            for (busy_start, busy_end) in participant_busy:
                # Check if [start, end) overlaps with [busy_start, busy_end)
                if start < busy_end and end > busy_start:
                    conflict = True
                    break
            if conflict:
                slot_ok = False
                break
        
        if slot_ok:
            found_slot = (start, end)
            break
    
    if found_slot:
        start_min, end_min = found_slot
        # Convert minutes to time strings (HH:MM format)
        def format_time(minutes):
            total_minutes = minutes
            hour = 9 + total_minutes // 60
            minute = total_minutes % 60
            return f"{hour:02d}:{minute:02d}"
        
        start_str = format_time(start_min)
        end_str = format_time(end_min)
        time_range_str = f"{start_str}:{end_str}"
        print("Monday")
        print(time_range_str)
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()