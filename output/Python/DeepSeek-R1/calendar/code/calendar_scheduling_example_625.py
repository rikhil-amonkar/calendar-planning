def find_meeting_time():
    work_hours = {'start': 9 * 60, 'end': 17 * 60}  # 9:00 to 17:00 in minutes
    meeting_duration = 30  # minutes

    # Harold's blocked times in minutes since midnight (Tuesday)
    harold_blocked_tuesday = [
        (9 * 60, 9 * 60 + 30),     # 09:00-09:30
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30-11:30
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30-13:30
        (14 * 60 + 30, 15 * 60 + 30),  # 14:30-15:30
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]
    
    # Check Tuesday after 14:30 first due to preference
    possible_slots = []
    
    # Check available slot between 15:30-16:00 on Tuesday
    start_candidate = 15 * 60 + 30  # 15:30
    end_candidate = start_candidate + meeting_duration
    if end_candidate <= 16 * 60:
        # Check against blocked times
        conflict = False
        for block_start, block_end in harold_blocked_tuesday:
            if start_candidate < block_end and end_candidate > block_start:
                conflict = True
                break
        if not conflict:
            possible_slots.append(('Tuesday', start_candidate, end_candidate))
    
    if possible_slots:
        day, start, end = possible_slots[0]
        return f"{day}: {format_time(start)}-{format_time(end)}"
    
    # If Tuesday not possible, check Monday (though preference is to avoid)
    harold_blocked_monday = [
        (9 * 60, 10 * 60),       # 09:00-10:00
        (10 * 60 + 30, 17 * 60)  # 10:30-17:00
    ]
    # Check available slot between 10:00-10:30 on Monday
    start_candidate = 10 * 60  # 10:00
    end_candidate = start_candidate + meeting_duration
    if end_candidate <= 10 * 60 + 30:
        conflict = False
        for block_start, block_end in harold_blocked_monday:
            if start_candidate < block_end and end_candidate > block_start:
                conflict = True
                break
        if not conflict:
            return f"Monday: {format_time(start_candidate)}-{format_time(end_candidate)}"
    
    return "No suitable time found"

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

result = find_meeting_time()
print(result)