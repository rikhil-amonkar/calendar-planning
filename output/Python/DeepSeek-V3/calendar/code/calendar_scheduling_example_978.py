from typing import Dict, List, Tuple

def find_meeting_time(brian_busy: Dict[str, List[Tuple[str, str]]], 
                     julia_busy: Dict[str, List[Tuple[str, str]]], 
                     duration: int = 60,
                     work_hours: Tuple[str, str] = ('09:00', '17:00'),
                     days_order: List[str] = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday'],
                     brian_avoid_days: List[str] = ['Monday']) -> Tuple[str, str]:
    """
    Finds the earliest available meeting time for Brian and Julia.
    
    Args:
        brian_busy: Dictionary mapping days to list of busy time ranges for Brian.
        julia_busy: Dictionary mapping days to list of busy time ranges for Julia.
        duration: Duration of the meeting in minutes.
        work_hours: Tuple of start and end time of work hours in 'HH:MM' format.
        days_order: List of days in order to check.
        brian_avoid_days: List of days Brian wants to avoid.
    
    Returns:
        A tuple of (day, time_range) where time_range is in 'HH:MM-HH:MM' format.
    """
    def time_to_minutes(time_str: str) -> int:
        """Converts 'HH:MM' time string to minutes since midnight."""
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes: int) -> str:
        """Converts minutes since midnight to 'HH:MM' time string."""
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    def merge_busy_slots(busy_slots: List[Tuple[str, str]]) -> List[Tuple[int, int]]:
        """Merges overlapping or adjacent busy slots and converts to minutes."""
        if not busy_slots:
            return []
        # Convert to minutes and sort
        slots = [(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_slots]
        slots.sort()
        merged = [slots[0]]
        for current_start, current_end in slots[1:]:
            last_start, last_end = merged[-1]
            if current_start <= last_end:
                # Overlapping or adjacent, merge them
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append((current_start, current_end))
        return merged
    
    work_start, work_end = map(time_to_minutes, work_hours)
    
    for day in days_order:
        if day in brian_avoid_days:
            continue
        
        # Get busy slots for both participants
        brian_day_slots = brian_busy.get(day, [])
        julia_day_slots = julia_busy.get(day, [])
        
        # Merge and combine busy slots
        brian_merged = merge_busy_slots(brian_day_slots)
        julia_merged = merge_busy_slots(julia_day_slots)
        
        # Combine all busy slots and sort
        all_busy = brian_merged + julia_merged
        all_busy.sort()
        
        # Find available slots
        prev_end = work_start
        available_slots = []
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                available_slots.append((prev_end, busy_start))
            prev_end = max(prev_end, busy_end)
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Check for a slot that can fit the meeting
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration:
                meeting_start = slot_start
                meeting_end = meeting_start + duration
                time_range = f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}"
                return (day, time_range)
    
    return ("No day found", "")

# Define busy schedules
brian_busy = {
    'Monday': [('9:30', '10:00'), ('12:30', '14:30'), ('15:30', '16:00')],
    'Tuesday': [('9:00', '9:30')],
    'Wednesday': [('12:30', '14:00'), ('16:30', '17:00')],
    'Thursday': [('11:00', '11:30'), ('13:00', '13:30'), ('16:30', '17:00')],
    'Friday': [('9:30', '10:00'), ('10:30', '11:00'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')]
}

julia_busy = {
    'Monday': [('9:00', '10:00'), ('11:00', '11:30'), ('12:30', '13:00'), ('15:30', '16:00')],
    'Tuesday': [('13:00', '14:00'), ('16:00', '16:30')],
    'Wednesday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:00', '17:00')],
    'Thursday': [('9:00', '10:30'), ('11:00', '17:00')],
    'Friday': [('9:00', '10:00'), ('10:30', '11:30'), ('12:30', '14:00'), ('14:30', '15:00'), ('15:30', '16:00')]
}

# Find meeting time
day, time_range = find_meeting_time(brian_busy, julia_busy, duration=60, brian_avoid_days=['Monday'])

# Output the result
start_time, end_time = time_range.split('-')
print(f"{day} {start_time}:{end_time}")