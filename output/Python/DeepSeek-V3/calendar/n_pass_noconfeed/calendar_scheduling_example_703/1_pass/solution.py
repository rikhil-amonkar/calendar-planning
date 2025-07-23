from typing import List, Dict, Tuple

def schedule_meeting(participants: List[str], 
                    days: List[str], 
                    work_hours: Tuple[str, str], 
                    duration: int,
                    constraints: Dict[str, Dict[str, List[str]]]) -> Dict[str, str]:
    """
    Schedule a meeting between participants based on their schedules and constraints.
    
    Args:
        participants: List of participant names.
        days: List of days to consider (e.g., ['Monday', 'Tuesday', 'Wednesday']).
        work_hours: Tuple of start and end time in 'HH:MM' format (e.g., ('9:00', '17:00')).
        duration: Duration of the meeting in minutes.
        constraints: Dictionary with participant names as keys and their schedules/preferences.
                     Example: {
                         'Stephanie': {
                             'schedule': {
                                 'Monday': ['9:30-10:00', '10:30-11:00', ...],
                                 'Tuesday': [...],
                                 ...
                             },
                             'preferences': ['Avoid Monday']
                         },
                         'Betty': {
                             'schedule': {...},
                             'preferences': ['No Tuesday after 12:30']
                         }
                     }
    
    Returns:
        A dictionary with 'day' and 'time_range' keys if a slot is found, otherwise None.
    """
    
    def time_to_minutes(time_str: str) -> int:
        """Convert 'HH:MM' time string to minutes since midnight."""
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    def minutes_to_time(minutes: int) -> str:
        """Convert minutes since midnight to 'HH:MM' time string."""
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = duration
    
    # Iterate through each day and find available slots
    for day in days:
        # Check if day is avoided by any participant
        avoid_day = False
        for participant in participants:
            prefs = constraints[participant].get('preferences', [])
            if f"Avoid {day}" in prefs:
                avoid_day = True
                break
        if avoid_day:
            continue
        
        # Collect all busy intervals for the day
        busy_intervals = []
        for participant in participants:
            schedule = constraints[participant]['schedule'].get(day, [])
            for interval in schedule:
                start, end = interval.split('-')
                start_min = time_to_minutes(start)
                end_min = time_to_minutes(end)
                busy_intervals.append((start_min, end_min))
        
        # Add constraints like "No Tuesday after 12:30"
        for participant in participants:
            prefs = constraints[participant].get('preferences', [])
            for pref in prefs:
                if pref.startswith("No ") and day in pref:
                    time_part = pref.split("after ")[1]
                    cutoff_min = time_to_minutes(time_part)
                    busy_intervals.append((cutoff_min, work_end_min))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find available slots
        available_slots = []
        prev_end = work_start_min
        
        for start, end in busy_intervals:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end_min:
            available_slots.append((prev_end, work_end_min))
        
        # Check for a slot that can fit the duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration_min:
                meeting_start = slot_start
                meeting_end = meeting_start + duration_min
                return {
                    'day': day,
                    'time_range': f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}"
                }
    
    return None

# Example usage
if __name__ == "__main__":
    participants = ["Stephanie", "Betty"]
    days = ["Monday", "Tuesday", "Wednesday"]
    work_hours = ("9:00", "17:00")
    duration = 60  # 1 hour
    
    constraints = {
        "Stephanie": {
            "schedule": {
                "Monday": ["9:30-10:00", "10:30-11:00", "11:30-12:00", "14:00-14:30"],
                "Tuesday": ["12:00-13:00"],
                "Wednesday": ["9:00-10:00", "13:00-14:00"]
            },
            "preferences": ["Avoid Monday"]
        },
        "Betty": {
            "schedule": {
                "Monday": ["9:00-10:00", "11:00-11:30", "14:30-15:00", "15:30-16:00"],
                "Tuesday": ["9:00-9:30", "11:30-12:00", "12:30-14:30", "15:30-16:00"],
                "Wednesday": ["10:00-11:30", "12:00-14:00", "14:30-17:00"]
            },
            "preferences": ["No Tuesday after 12:30"]
        }
    }
    
    result = schedule_meeting(participants, days, work_hours, duration, constraints)
    if result:
        day = result['day']
        time_range = result['time_range']
        start, end = time_range.split('-')
        print(f"{day}: {start}-{end}")
    else:
        print("No suitable time slot found.")