def find_meeting_time(participants_schedules, meeting_duration_minutes, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of the day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Generate all possible time slots within work hours
    all_slots = []
    current_time = work_start
    while current_time + meeting_duration_minutes <= work_end:
        all_slots.append((current_time, current_time + meeting_duration_minutes))
        current_time += 1  # Check every minute
    
    # Check each slot against all participants' schedules
    for slot_start, slot_end in all_slots:
        slot_ok = True
        for participant, blocked_slots in participants_schedules.items():
            for blocked_start, blocked_end in blocked_slots:
                blocked_start_min = time_to_minutes(blocked_start)
                blocked_end_min = time_to_minutes(blocked_end)
                # Check if slot overlaps with any blocked time
                if not (slot_end <= blocked_start_min or slot_start >= blocked_end_min):
                    slot_ok = False
                    break
            if not slot_ok:
                break
        if slot_ok:
            return (minutes_to_time(slot_start), minutes_to_time(slot_end)
    return None

# Define participants' schedules
participants_schedules = {
    'Diane': [('09:30', '10:00'), ('14:30', '15:00')],
    'Jack': [('13:30', '14:00'), ('14:30', '15:00')],
    'Eugene': [('09:00', '10:00'), ('10:30', '11:30'), ('12:00', '14:30'), ('15:00', '16:30')],
    'Patricia': [('09:30', '10:30'), ('11:00', '12:00'), ('12:30', '14:00'), ('15:00', '16:30')]
}

# Meeting constraints
meeting_duration_minutes = 30
work_hours_start = '09:00'
work_hours_end = '17:00'
day_of_week = 'Monday'

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration_minutes, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{day_of_week}: {start_time} - {end_time}")
else:
    print("No suitable time found.")