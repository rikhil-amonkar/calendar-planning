def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Margaret's constraints (in minutes since midnight)
    margaret_unavailable = {
        'Monday': [
            (10 * 60 + 30, 11 * 60 + 0),
            (11 * 60 + 30, 12 * 60 + 0),
            (13 * 60 + 0, 13 * 60 + 30),
            (15 * 60 + 0, 17 * 60 + 0)
        ],
        'Tuesday': [
            (12 * 60 + 0, 12 * 60 + 30)
        ]
    }
    
    # Alexis's constraints (in minutes since midnight)
    alexis_unavailable = {
        'Monday': [
            (9 * 60 + 30, 11 * 60 + 30),
            (12 * 60 + 30, 13 * 60 + 0),
            (14 * 60 + 0, 17 * 60 + 0)
        ],
        'Tuesday': [
            (9 * 60 + 0, 9 * 60 + 30),
            (10 * 60 + 0, 10 * 60 + 30),
            (14 * 60 + 0, 16 * 60 + 30)
        ]
    }
    
    # Margaret's preferences: not Monday, and Tuesday before 14:30
    preferred_day = 'Tuesday'
    margaret_preferred_start = 14 * 60 + 30  # 14:30
    
    meeting_duration = 30  # minutes
    
    # Check Tuesday first (preferred day)
    day = preferred_day
    # Generate available slots for Margaret and Alexis on Tuesday
    margaret_slots = []
    alexis_slots = []
    
    # Margaret's available times on Tuesday (after 14:30)
    margaret_busy = margaret_unavailable.get(day, [])
    margaret_busy.append((0, margaret_preferred_start))  # Block before 14:30
    margaret_busy.sort()
    
    # Find Margaret's available slots
    prev_end = work_start
    for start, end in margaret_busy:
        if start > prev_end:
            margaret_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        margaret_slots.append((prev_end, work_end))
    
    # Alexis's available times on Tuesday
    alexis_busy = alexis_unavailable.get(day, [])
    alexis_busy.sort()
    
    prev_end = work_start
    for start, end in alexis_busy:
        if start > prev_end:
            alexis_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        alexis_slots.append((prev_end, work_end))
    
    # Find overlapping slots
    for m_start, m_end in margaret_slots:
        for a_start, a_end in alexis_slots:
            overlap_start = max(m_start, a_start)
            overlap_end = min(m_end, a_end)
            if overlap_end - overlap_start >= meeting_duration:
                # Found a suitable slot
                start_time = overlap_start
                end_time = start_time + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
                print(f"{start_str}:{end_str}")
                print(day)
                return
    
    # If no slot found on Tuesday (shouldn't happen per problem statement)
    print("No suitable time found.")

find_meeting_time()