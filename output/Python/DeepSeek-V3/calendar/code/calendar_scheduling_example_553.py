def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Convert blocked times to minutes since midnight
    eric_blocked = [
        (12 * 60, 13 * 60),  # 12:00-13:00
        (14 * 60, 15 * 60)   # 14:00-15:00
    ]
    henry_blocked = [
        (9 * 60 + 30, 10 * 60),    # 9:30-10:00
        (10 * 60 + 30, 11 * 60),   # 10:30-11:00
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30-12:30
        (13 * 60, 13 * 60 + 30),    # 13:00-13:30
        (14 * 60 + 30, 15 * 60),   # 14:30-15:00
        (16 * 60, 17 * 60)          # 16:00-17:00
    ]
    henry_preference_end = 10 * 60  # Prefers not to meet after 10:00

    # Combine all blocked times for both participants
    all_blocked = []
    for block in eric_blocked:
        all_blocked.append(('Eric', block[0], block[1]))
    for block in henry_blocked:
        all_blocked.append(('Henry', block[0], block[1]))
    # Sort blocked times by start time
    all_blocked.sort(key=lambda x: x[1])

    # Find available slots before Henry's preference end time
    current_time = work_start
    for block in all_blocked:
        start, end = block[1], block[2]
        if start > current_time:
            available_start = current_time
            available_end = min(start, henry_preference_end)
            if available_end - available_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = available_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
                print("Monday")
                return
        current_time = max(current_time, end)
    
    # Check after current_time but before henry_preference_end
    if henry_preference_end - current_time >= meeting_duration:
        meeting_start = current_time
        meeting_end = meeting_start + meeting_duration
        start_hh = meeting_start // 60
        start_mm = meeting_start % 60
        end_hh = meeting_end // 60
        end_mm = meeting_end % 60
        print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
        print("Monday")
        return
    
    # If no slot found before preference, look after (even though Henry prefers not to)
    current_time = work_start
    for block in all_blocked:
        start, end = block[1], block[2]
        if start > current_time:
            available_start = current_time
            available_end = start
            if available_end - available_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = available_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
                print("Monday")
                return
        current_time = max(current_time, end)
    
    # Check after last blocked time
    if work_end - current_time >= meeting_duration:
        meeting_start = current_time
        meeting_end = meeting_start + meeting_duration
        start_hh = meeting_start // 60
        start_mm = meeting_start % 60
        end_hh = meeting_end // 60
        end_mm = meeting_end % 60
        print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
        print("Monday")
        return
    
    print("No suitable time found.")

find_meeting_time()