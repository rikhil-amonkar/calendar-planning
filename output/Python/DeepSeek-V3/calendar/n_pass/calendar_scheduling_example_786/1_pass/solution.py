from datetime import datetime, timedelta

def find_meeting_time(participants, days, work_hours_start, work_hours_end, duration, preferences):
    """
    Find a suitable meeting time based on participants' schedules and preferences.
    
    Args:
        participants: Dict of participant names to their busy times per day.
        days: List of days to consider (e.g., ['Monday', 'Tuesday', 'Wednesday']).
        work_hours_start: Start of workday in 'HH:MM' format.
        work_hours_end: End of workday in 'HH:MM' format.
        duration: Meeting duration in minutes.
        preferences: Dict of participant names to their time preferences (avoidance rules).
    
    Returns:
        Tuple of (day, start_time, end_time) or None if no time found.
    """
    duration = timedelta(minutes=duration)
    work_start = datetime.strptime(work_hours_start, '%H:%M').time()
    work_end = datetime.strptime(work_hours_end, '%H:%M').time()
    
    for day in days:
        # Collect all busy intervals for the day across participants
        busy_intervals = []
        for name, schedule in participants.items():
            if day in schedule:
                busy_intervals.extend(schedule[day])
        
        # Add preferences as busy intervals (e.g., avoid before 16:00)
        for name, pref in preferences.items():
            if day in pref.get('avoid_days', []):
                # Entire day is avoided
                busy_intervals.append((work_start, work_end))
            if 'before' in pref and day in pref.get('avoid_days_before', []):
                avoid_until = datetime.strptime(pref['before'], '%H:%M').time()
                busy_intervals.append((work_start, avoid_until))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find free slots by checking gaps between busy intervals
        prev_end = work_start
        for start, end in busy_intervals:
            if start > prev_end:
                # Check if the gap is long enough
                gap_start = prev_end
                gap_end = start
                if (datetime.combine(datetime.today(), gap_end) - 
                    datetime.combine(datetime.today(), gap_start) >= duration):
                    return day, gap_start, gap_end
            prev_end = max(prev_end, end)
        
        # Check after last busy interval
        if prev_end < work_end:
            gap_start = prev_end
            gap_end = work_end
            if (datetime.combine(datetime.today(), gap_end) - 
                datetime.combine(datetime.today(), gap_start) >= duration):
                return day, gap_start, gap_end
    
    return None

# Define participants' schedules
participants = {
    'Amy': {
        'Wednesday': [
            (datetime.strptime('11:00', '%H:%M').time(), datetime.strptime('11:30', '%H:%M').time()),
            (datetime.strptime('13:30', '%H:%M').time(), datetime.strptime('14:00', '%H:%M').time()),
        ]
    },
    'Pamela': {
        'Monday': [
            (datetime.strptime('9:00', '%H:%M').time(), datetime.strptime('10:30', '%H:%M').time()),
            (datetime.strptime('11:00', '%H:%M').time(), datetime.strptime('16:30', '%H:%M').time()),
        ],
        'Tuesday': [
            (datetime.strptime('9:00', '%H:%M').time(), datetime.strptime('9:30', '%H:%M').time()),
            (datetime.strptime('10:00', '%H:%M').time(), datetime.strptime('17:00', '%H:%M').time()),
        ],
        'Wednesday': [
            (datetime.strptime('9:00', '%H:%M').time(), datetime.strptime('9:30', '%H:%M').time()),
            (datetime.strptime('10:00', '%H:%M').time(), datetime.strptime('11:00', '%H:%M').time()),
            (datetime.strptime('11:30', '%H:%M').time(), datetime.strptime('13:30', '%H:%M').time()),
            (datetime.strptime('14:30', '%H:%M').time(), datetime.strptime('15:00', '%H:%M').time()),
            (datetime.strptime('16:00', '%H:%M').time(), datetime.strptime('16:30', '%H:%M').time()),
        ]
    }
}

# Define preferences
preferences = {
    'Pamela': {
        'avoid_days': ['Monday'],  # Avoid more meetings on Monday
        'avoid_days_before': ['Tuesday', 'Wednesday'],  # Avoid before 16:00 on these days
        'before': '16:00'
    }
}

# Define meeting parameters
days = ['Monday', 'Tuesday', 'Wednesday']
work_hours_start = '9:00'
work_hours_end = '17:00'
duration = 30  # minutes

# Find meeting time
result = find_meeting_time(participants, days, work_hours_start, work_hours_end, duration, preferences)

if result:
    day, start_time, end_time = result
    # Format output as HH:MM:HH:MM and day
    start_str = start_time.strftime('%H:%M')
    end_str = end_time.strftime('%H:%M')
    print(f"{day}: {{{start_str}:{end_str}}}")
else:
    print("No suitable time found.")