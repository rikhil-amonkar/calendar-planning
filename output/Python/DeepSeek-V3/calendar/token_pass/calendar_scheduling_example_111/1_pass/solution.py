def schedule_meeting():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Busy times in minutes from start of day (9:00 = 0)
    # Convert each time to minutes since 9:00
    def t(h, m):
        return h * 60 + m - 9 * 60
    
    # Gregory's busy times (relative to 9:00)
    gregory_busy = [
        (t(9, 0), t(10, 0)),
        (t(10, 30), t(11, 30)),
        (t(12, 30), t(13, 0)),
        (t(13, 30), t(14, 0))
    ]
    
    # Natalie's busy times
    natalie_busy = []  # None
    
    # Christine's busy times
    christine_busy = [
        (t(9, 0), t(11, 30)),
        (t(13, 30), t(17, 0))
    ]
    
    # Vincent's busy times
    vincent_busy = [
        (t(9, 0), t(9, 30)),
        (t(10, 30), t(12, 0)),
        (t(12, 30), t(14, 0)),
        (t(14, 30), t(17, 0))
    ]
    
    # Combine all busy times
    all_busy = gregory_busy + natalie_busy + christine_busy + vincent_busy
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    for start, end in all_busy:
        if not merged or merged[-1][1] < start:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)
    
    # Find first available 30-minute slot
    meeting_duration = 30
    current_time = 0  # 9:00
    
    for busy_start, busy_end in merged:
        if current_time + meeting_duration <= busy_start:
            # Found a slot
            slot_start = current_time
            slot_end = slot_start + meeting_duration
            # Convert back to actual time
            def to_time(minutes):
                total_minutes = 9 * 60 + minutes
                h = total_minutes // 60
                m = total_minutes % 60
                return f"{h:02d}:{m:02d}"
            
            start_str = to_time(slot_start)
            end_str = to_time(slot_end)
            return "Monday", f"{start_str}:{end_str}"
        
        # Move current_time to after this busy period
        if current_time < busy_end:
            current_time = busy_end
    
    # Check after last busy period
    if current_time + meeting_duration <= work_end - work_start:
        slot_start = current_time
        slot_end = slot_start + meeting_duration
        def to_time(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = to_time(slot_start)
        end_str = to_time(slot_end)
        return "Monday", f"{start_str}:{end_str}"
    
    return None, None

def main():
    day, time_range = schedule_meeting()
    if day and time_range:
        print(f"{day}:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()