def find_meeting_time(participants_busy_times, work_hours_start, work_hours_end, meeting_duration):
    # Convert all times to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Generate all possible slots within work hours
    slots = []
    current = work_start
    while current + meeting_duration <= work_end:
        slots.append((current, current + meeting_duration))
        current += 1  # Check every minute
    
    # Check each slot against all participants' busy times
    for slot_start, slot_end in slots:
        slot_ok = True
        for busy_times in participants_busy_times:
            for busy_start, busy_end in busy_times:
                busy_start_min = time_to_minutes(busy_start)
                busy_end_min = time_to_minutes(busy_end)
                # Check if slot overlaps with any busy time
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    slot_ok = False
                    break
            if not slot_ok:
                break
        if slot_ok:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            return (minutes_to_time(slot_start), minutes_to_time(slot_end))
    return None

# Define work hours and meeting duration
work_hours_start = "9:00"
work_hours_end = "17:00"
meeting_duration = 60  # minutes

# Participants' busy times in HH:MM format
participants_busy_times = [
    [("11:00", "12:30"), ("13:30", "14:30"), ("16:30", "17:00")],  # Joshua
    [],  # Kevin
    [],  # Gerald
    [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],  # Jerry
    [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("15:30", "16:30")],  # Jesse
    [("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],  # Kenneth
]

# Find a meeting time
meeting_time = find_meeting_time(participants_busy_times, work_hours_start, work_hours_end, meeting_duration)

if meeting_time:
    start, end = meeting_time
    print(f"{start}:{end}")
    print("Monday")
else:
    print("No suitable time found.")