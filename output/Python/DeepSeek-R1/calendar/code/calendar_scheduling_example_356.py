def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def find_meeting_time(schedules, duration, work_hours, preferences):
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    
    # Create timeline for the day
    timeline = []
    current = work_start
    while current + duration <= work_end:
        timeline.append((current, current + duration))
        current += 1  # Check every minute
    
    # Filter by preferences
    pref_start = parse_time(preferences.get('preferred_after', '00:00'))
    timeline = [slot for slot in timeline if slot[0] >= pref_start]
    
    # Check availability for each slot
    for slot_start, slot_end in timeline:
        all_available = True
        for person, busy_slots in schedules.items():
            for busy_start, busy_end in busy_slots:
                busy_start_min = parse_time(busy_start)
                busy_end_min = parse_time(busy_end)
                # Check if slot overlaps with any busy period
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    all_available = False
                    break
            if not all_available:
                break
        if all_available:
            return (slot_start, slot_end)
    return None

# Define schedules
schedules = {
    'Katherine': [('12:00', '12:30'), ('13:00', '14:30')],
    'Rebecca': [],
    'Julie': [('09:00', '09:30'), ('10:30', '11:00'), ('13:30', '14:00'), ('15:00', '15:30')],
    'Angela': [('09:00', '10:00'), ('10:30', '11:00'), ('11:30', '14:00'), ('14:30', '15:00'), ('16:30', '17:00')],
    'Nicholas': [('09:30', '11:00'), ('11:30', '13:30'), ('14:00', '16:00'), ('16:30', '17:00')],
    'Carl': [('09:00', '11:00'), ('11:30', '12:30'), ('13:00', '14:30'), ('15:00', '16:00'), ('16:30', '17:00')]
}

# Angela's preference to avoid before 15:00
preferences = {'preferred_after': '15:00'}

# Find meeting time
meeting_time = find_meeting_time(
    schedules,
    duration=30,
    work_hours=('09:00', '17:00'),
    preferences=preferences
)

# Format output
if meeting_time:
    start = format_time(meeting_time[0])
    end = format_time(meeting_time[1])
    print(f"Monday:{start}:{end}")
else:
    print("No suitable time found")