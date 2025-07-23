from typing import List, Dict, Tuple

def find_meeting_time(participants: Dict[str, Dict[str, List[Tuple[str, str]]]], 
                     days: List[str], 
                     work_hours: Tuple[str, str], 
                     duration_minutes: int) -> Tuple[str, str]:
    """
    Finds the earliest available meeting time for participants given their schedules.
    
    Args:
        participants: Dictionary of participant names to their blocked times per day.
        days: List of days to consider (e.g., ['Monday', 'Tuesday']).
        work_hours: Tuple of start and end time in 'HH:MM' format (e.g., ('9:00', '17:00')).
        duration_minutes: Duration of the meeting in minutes.
    
    Returns:
        Tuple of (day, time_range) where time_range is in 'HH:MM-HH:MM' format.
    """
    # Convert work hours to minutes since midnight
    work_start = convert_time_to_minutes(work_hours[0])
    work_end = convert_time_to_minutes(work_hours[1])
    
    for day in days:
        # Collect all blocked intervals for the day across participants
        all_blocked = []
        for person, schedule in participants.items():
            if day in schedule:
                for start, end in schedule[day]:
                    all_blocked.append((convert_time_to_minutes(start), convert_time_to_minutes(end)))
        
        # Sort blocked intervals by start time
        all_blocked.sort()
        
        # Merge overlapping or adjacent blocked intervals
        merged_blocked = []
        for start, end in all_blocked:
            if not merged_blocked:
                merged_blocked.append((start, end))
            else:
                last_start, last_end = merged_blocked[-1]
                if start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged_blocked[-1] = (new_start, new_end)
                else:
                    merged_blocked.append((start, end))
        
        # Check the time before the first blocked interval
        if merged_blocked:
            first_start, _ = merged_blocked[0]
            if first_start - work_start >= duration_minutes:
                meeting_start = work_start
                meeting_end = meeting_start + duration_minutes
                return (day, format_time_range(meeting_start, meeting_end))
        
        # Check the time between blocked intervals
        for i in range(len(merged_blocked) - 1):
            _, current_end = merged_blocked[i]
            next_start, _ = merged_blocked[i + 1]
            if next_start - current_end >= duration_minutes:
                meeting_start = current_end
                meeting_end = meeting_start + duration_minutes
                return (day, format_time_range(meeting_start, meeting_end))
        
        # Check the time after the last blocked interval
        if merged_blocked:
            _, last_end = merged_blocked[-1]
            if work_end - last_end >= duration_minutes:
                meeting_start = last_end
                meeting_end = meeting_start + duration_minutes
                return (day, format_time_range(meeting_start, meeting_end))
        else:
            # No blocked intervals, the whole workday is free
            meeting_start = work_start
            meeting_end = meeting_start + duration_minutes
            return (day, format_time_range(meeting_start, meeting_end))
    
    raise ValueError("No suitable time found.")

def convert_time_to_minutes(time_str: str) -> int:
    """Converts 'HH:MM' time string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time_range(start_minutes: int, end_minutes: int) -> str:
    """Converts minutes since midnight to 'HH:MM-HH:MM' format."""
    start_hh = start_minutes // 60
    start_mm = start_minutes % 60
    end_hh = end_minutes // 60
    end_mm = end_minutes % 60
    return f"{start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}"

# Define participants' schedules
participants = {
    "Ronald": {
        "Monday": [("10:30", "11:00"), ("12:00", "12:30"), ("15:30", "16:00")],
        "Tuesday": [("9:00", "9:30"), ("12:00", "12:30"), ("15:30", "16:30")],
        "Wednesday": [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")],
    },
    "Amber": {
        "Monday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:30"), ("16:30", "17:00")],
        "Wednesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "13:30"), ("15:00", "15:30")],
    },
}

# Define task constraints
days = ["Monday", "Tuesday", "Wednesday"]
work_hours = ("9:00", "17:00")
duration_minutes = 30

# Find the earliest meeting time
day, time_range = find_meeting_time(participants, days, work_hours, duration_minutes)
print(f"{day}: {time_range}")