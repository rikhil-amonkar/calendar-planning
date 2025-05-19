def find_meeting_time():
    participants = {
        'Daniel': [],
        'Kathleen': [('14:30', '15:30')],
        'Carolyn': [('12:00', '12:30'), ('13:00', '13:30')],
        'Roger': [],
        'Cheryl': [('09:00', '09:30'), ('10:00', '11:30'), ('12:30', '13:30'), ('14:00', '17:00')],
        'Virginia': [('09:30', '11:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:30', '15:30'), ('16:00', '17:00')],
        'Angela': [('09:30', '10:00'), ('10:30', '11:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:00', '16:30')]
    }
    
    # Roger's constraint: not before 12:30
    roger_constraint = ('12:30', '17:00')
    
    # Work hours
    work_start = '09:00'
    work_end = '17:00'
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Convert time string to minutes since 00:00 for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    # Generate all busy intervals for all participants
    busy_intervals = []
    for person, intervals in participants.items():
        for start, end in intervals:
            busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Add Roger's constraint as a busy interval before 12:30
    roger_constraint_start = time_to_minutes(roger_constraint[0])
    busy_intervals.append((time_to_minutes(work_start), roger_constraint_start))
    
    # Sort intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_end = max(end, last_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append((start, end))
    
    # Find free slots between merged busy intervals
    free_slots = []
    previous_end = time_to_minutes(work_start)
    for start, end in merged:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < time_to_minutes(work_end):
        free_slots.append((previous_end, time_to_minutes(work_end)))
    
    # Filter free slots that can accommodate the meeting duration
    possible_slots = []
    for start, end in free_slots:
        if end - start >= meeting_duration:
            possible_slots.append((start, end))
    
    # Select the earliest possible slot
    if possible_slots:
        meeting_start = possible_slots[0][0]
        meeting_end = meeting_start + meeting_duration
        meeting_time = (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
        print(f"{meeting_time[0]}:{meeting_time[1]}")
        print("Monday")
    else:
        print("No suitable time found")

find_meeting_time()