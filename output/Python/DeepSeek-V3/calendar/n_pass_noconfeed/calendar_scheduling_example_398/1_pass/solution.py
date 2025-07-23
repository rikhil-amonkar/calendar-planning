def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_minutes
    
    # Initialize the free slots for the entire work day
    free_slots = [{'start': work_start, 'end': work_end}]
    
    # Process each participant's schedule to find common free slots
    for schedule in participants_schedules:
        new_free_slots = []
        for slot in free_slots:
            current_start = slot['start']
            # Apply each blocked time in the participant's schedule
            for block in schedule:
                block_start = time_to_minutes(block['start'])
                block_end = time_to_minutes(block['end'])
                # If the block overlaps with the current slot
                if block_start < slot['end'] and block_end > slot['start']:
                    # Add free time before the block if any
                    if block_start > current_start:
                        new_free_slots.append({'start': current_start, 'end': block_start})
                    current_start = max(current_start, block_end)
            # Add remaining free time after the last block if any
            if current_start < slot['end']:
                new_free_slots.append({'start': current_start, 'end': slot['end']})
        free_slots = new_free_slots
        if not free_slots:
            return None  # No common free time
    
    # Find the first slot that can accommodate the meeting duration
    for slot in free_slots:
        if slot['end'] - slot['start'] >= duration:
            meeting_start = slot['start']
            meeting_end = meeting_start + duration
            return {
                'day': day,
                'time_range': f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            }
    return None

# Define the participants' schedules
participants_schedules = [
    # Doris's schedule
    [
        {'start': '09:00', 'end': '11:00'},
        {'start': '13:30', 'end': '14:00'},
        {'start': '16:00', 'end': '16:30'}
    ],
    # Theresa's schedule
    [
        {'start': '10:00', 'end': '12:00'}
    ],
    # Christian's schedule (no meetings)
    [],
    # Terry's schedule
    [
        {'start': '09:30', 'end': '10:00'},
        {'start': '11:30', 'end': '12:00'},
        {'start': '12:30', 'end': '13:00'},
        {'start': '13:30', 'end': '14:00'},
        {'start': '14:30', 'end': '15:00'},
        {'start': '15:30', 'end': '17:00'}
    ],
    # Carolyn's schedule
    [
        {'start': '09:00', 'end': '10:30'},
        {'start': '11:00', 'end': '11:30'},
        {'start': '12:00', 'end': '13:00'},
        {'start': '13:30', 'end': '14:30'},
        {'start': '15:00', 'end': '17:00'}
    ],
    # Kyle's schedule
    [
        {'start': '09:00', 'end': '09:30'},
        {'start': '11:30', 'end': '12:00'},
        {'start': '12:30', 'end': '13:00'},
        {'start': '14:30', 'end': '17:00'}
    ]
]

# Find a meeting time
meeting_time = find_meeting_time(
    participants_schedules=participants_schedules,
    day="Monday",
    work_hours_start="09:00",
    work_hours_end="17:00",
    duration_minutes=30
)

# Output the result
if meeting_time:
    print(f"{meeting_time['day']}: {meeting_time['time_range']}")
else:
    print("No suitable meeting time found.")