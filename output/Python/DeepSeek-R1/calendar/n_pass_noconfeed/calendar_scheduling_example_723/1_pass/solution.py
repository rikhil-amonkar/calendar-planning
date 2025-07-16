def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_free(slot_start, slot_end, meetings):
    for meet_start, meet_end in meetings:
        if slot_start < meet_end and slot_end > meet_start:
            return False
    return True

# Define schedules in minutes
arthur_schedule = {
    'Monday': [
        (time_to_minutes('11:00'), time_to_minutes('11:30')),
        (time_to_minutes('13:30'), time_to_minutes('14:00')),
        (time_to_minutes('15:00'), time_to_minutes('15:30'))
    ],
    'Tuesday': [
        (time_to_minutes('13:00'), time_to_minutes('13:30')),
        (time_to_minutes('16:00'), time_to_minutes('16:30'))
    ],
    'Wednesday': [
        (time_to_minutes('10:00'), time_to_minutes('10:30')),
        (time_to_minutes('11:00'), time_to_minutes('11:30')),
        (time_to_minutes('12:00'), time_to_minutes('12:30')),
        (time_to_minutes('14:00'), time_to_minutes('14:30')),
        (time_to_minutes('16:00'), time_to_minutes('16:30'))
    ]
}

michael_schedule = {
    'Monday': [
        (time_to_minutes('9:00'), time_to_minutes('12:00')),
        (time_to_minutes('12:30'), time_to_minutes('13:00')),
        (time_to_minutes('14:00'), time_to_minutes('14:30')),
        (time_to_minutes('15:00'), time_to_minutes('17:00'))
    ],
    'Tuesday': [
        (time_to_minutes('9:30'), time_to_minutes('11:30')),
        (time_to_minutes('12:00'), time_to_minutes('13:30')),
        (time_to_minutes('14:00'), time_to_minutes('15:30'))
    ],
    'Wednesday': [
        (time_to_minutes('10:00'), time_to_minutes('12:30')),
        (time_to_minutes('13:00'), time_to_minutes('13:30'))
    ]
}

days_to_check = ['Monday', 'Wednesday']
work_start = time_to_minutes('9:00')
work_end = time_to_minutes('17:00')
duration = 30

for day in days_to_check:
    arthur_meetings = arthur_schedule.get(day, [])
    michael_meetings = michael_schedule.get(day, [])
    
    slot_start = work_start
    while slot_start + duration <= work_end:
        slot_end = slot_start + duration
        
        arthur_free = is_free(slot_start, slot_end, arthur_meetings)
        michael_free = is_free(slot_start, slot_end, michael_meetings)
        
        if arthur_free and michael_free:
            start_time_str = minutes_to_time(slot_start)
            end_time_str = minutes_to_time(slot_end)
            time_range_str = f"{start_time_str}:{end_time_str}"
            print(day)
            print(time_range_str)
            exit(0)
        
        slot_start += 30

# Since there is guaranteed to be a solution, this exit may not be reached.
print("No suitable time found")