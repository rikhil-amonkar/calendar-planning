from typing import List, Dict, Tuple

def find_meeting_time(participants: Dict[str, Dict[str, List[Tuple[str, str]]]], 
                     days: List[str], 
                     work_hours: Tuple[str, str], 
                     duration: int, 
                     preferences: Dict[str, Dict[str, List[str]]] = None) -> Tuple[str, str]:
    """
    Finds a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants: A dictionary where keys are participant names and values are dictionaries
                     with days as keys and lists of busy time slots (as tuples of start and end times) as values.
        days: List of days to consider for the meeting (e.g., ['Monday', 'Tuesday']).
        work_hours: Tuple of start and end times for the workday (e.g., ('9:00', '17:00')).
        duration: Duration of the meeting in minutes.
        preferences: Optional dictionary of preferences (e.g., {'Doris': {'Monday': ['before 14:00']}}).
    
    Returns:
        A tuple of (day, time_slot) where time_slot is in the format 'HH:MM-HH:MM'.
    """
    # Convert work hours to minutes
    work_start = convert_time_to_minutes(work_hours[0])
    work_end = convert_time_to_minutes(work_hours[1])
    
    for day in days:
        # Collect all busy slots for the day across participants
        busy_slots = []
        for name, schedule in participants.items():
            if day in schedule:
                busy_slots.extend([(convert_time_to_minutes(start), convert_time_to_minutes(end)) 
                                  for start, end in schedule[day]])
        
        # Add preferences as busy slots if applicable
        if preferences:
            for name, pref in preferences.items():
                if day in pref:
                    for constraint in pref[day]:
                        if constraint == 'before 14:00':
                            busy_slots.append((convert_time_to_minutes('14:00'), work_end))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        
        for start, end in busy_slots:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check for a free slot that can fit the meeting
        for start, end in free_slots:
            if end - start >= duration:
                meeting_start = start
                meeting_end = meeting_start + duration
                time_slot = (f"{convert_minutes_to_time(meeting_start)}-{convert_minutes_to_time(meeting_end)}")
                return (day, time_slot)
    
    return (None, None)

def convert_time_to_minutes(time_str: str) -> int:
    """Converts a time string (HH:MM) to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_minutes_to_time(minutes: int) -> str:
    """Converts minutes since midnight to a time string (HH:MM)."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the problem
participants = {
    'Jean': {
        'Tuesday': [('11:30', '12:00'), ('16:00', '16:30')]
    },
    'Doris': {
        'Monday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:30', '16:00'), ('16:30', '17:00')],
        'Tuesday': [('9:00', '17:00')]
    }
}

days = ['Monday', 'Tuesday']
work_hours = ('9:00', '17:00')
duration = 30  # minutes
preferences = {
    'Doris': {
        'Monday': ['before 14:00']
    }
}

# Find the meeting time
day, time_slot = find_meeting_time(participants, days, work_hours, duration, preferences)

# Output the result
if day and time_slot:
    start, end = time_slot.split('-')
    print(f"{day}: {start}:{end}")
else:
    print("No suitable meeting time found.")