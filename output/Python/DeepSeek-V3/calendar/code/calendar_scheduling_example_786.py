from datetime import time

def find_meeting_time(participants_busy, preferences, days, work_hours_start, work_hours_end, duration):
    # Convert work hours to minutes for easier calculation
    start_min = work_hours_start.hour * 60 + work_hours_start.minute
    end_min = work_hours_end.hour * 60 + work_hours_end.minute
    duration_min = duration * 60

    for day in days:
        # Skip if day is in preferences to avoid
        if day in preferences.get('avoid_days', []):
            continue
        
        # Collect all busy intervals for the day
        busy_intervals = []
        for person, schedule in participants_busy.items():
            if day in schedule:
                for interval in schedule[day]:
                    start = interval[0].hour * 60 + interval[0].minute
                    end = interval[1].hour * 60 + interval[1].minute
                    busy_intervals.append((start, end))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find free slots
        free_slots = []
        prev_end = start_min
        
        for start, end in busy_intervals:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < end_min:
            free_slots.append((prev_end, end_min))
        
        # Check each free slot for duration and preferences
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= duration_min:
                proposed_start = slot_start
                proposed_end = proposed_start + duration_min
                
                # Check if proposed time is before avoid_before time in preferences
                avoid_before = preferences.get('avoid_before', {}).get(day, 0)
                avoid_before_min = avoid_before.hour * 60 + avoid_before.minute if isinstance(avoid_before, time) else avoid_before * 60
                
                if proposed_start >= avoid_before_min:
                    # Convert back to HH:MM format
                    start_time = time(proposed_start // 60, proposed_start % 60)
                    end_time = time(proposed_end // 60, proposed_end % 60)
                    return day, start_time, end_time
    
    return None, None, None

# Define participants' busy schedules
participants_busy = {
    'Amy': {
        'Wednesday': [
            (time(11, 0), time(11, 30)),
            (time(13, 30), time(14, 0))
        ]
    },
    'Pamela': {
        'Monday': [
            (time(9, 0), time(10, 30)),
            (time(11, 0), time(16, 30))
        ],
        'Tuesday': [
            (time(9, 0), time(9, 30)),
            (time(10, 0), time(17, 0))
        ],
        'Wednesday': [
            (time(9, 0), time(9, 30)),
            (time(10, 0), time(11, 0)),
            (time(11, 30), time(13, 30)),
            (time(14, 30), time(15, 0)),
            (time(16, 0), time(16, 30))
        ]
    }
}

# Define preferences
preferences = {
    'avoid_days': ['Monday', 'Tuesday'],
    'avoid_before': {
        'Monday': time(16, 0),
        'Tuesday': time(16, 0),
        'Wednesday': time(16, 0)
    }
}

# Define meeting parameters
days_to_check = ['Monday', 'Tuesday', 'Wednesday']
work_start = time(9, 0)
work_end = time(17, 0)
meeting_duration = 0.5  # half hour

# Find meeting time
day, start_time, end_time = find_meeting_time(participants_busy, preferences, days_to_check, work_start, work_end, meeting_duration)

# Output the result
if day and start_time and end_time:
    print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
else:
    print("No suitable time found.")