from typing import List, Dict, Tuple

def find_earliest_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    days: List[str],
    work_hours: Tuple[str, str],
    duration_minutes: int
) -> Tuple[str, str]:
    # Convert time string "HH:MM" to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to "HH:MM"
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = map(time_to_minutes, work_hours)
    duration = duration_minutes
    
    for day in days:
        # Collect all busy intervals for the day for all participants
        busy_intervals = []
        for person, schedule in participants.items():
            if day in schedule:
                for start, end in schedule[day]:
                    start_min = time_to_minutes(start)
                    end_min = time_to_minutes(end)
                    busy_intervals.append((start_min, end_min))
        
        # Sort all busy intervals by start time
        busy_intervals.sort()
        
        # Find available slots between work hours considering all busy intervals
        available_slots = []
        prev_end = work_start
        
        for start, end in busy_intervals:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Check each available slot for sufficient duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration:
                meeting_start = slot_start
                meeting_end = meeting_start + duration
                return day, f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    
    return None, None

# Define the participants' schedules
participants = {
    "Mary": {
        "Tuesday": [("10:00", "10:30"), ("15:30", "16:00")],
        "Wednesday": [("9:30", "10:00"), ("15:00", "15:30")],
        "Thursday": [("9:00", "10:00"), ("10:30", "11:30")],
    },
    "Alexis": {
        "Monday": [("9:00", "10:00"), ("10:30", "12:00"), ("12:30", "16:30")],
        "Tuesday": [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("9:00", "11:00"), ("11:30", "17:00")],
        "Thursday": [("10:00", "12:00"), ("14:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    }
}

# Define the days to consider
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Define work hours and meeting duration
work_hours = ("9:00", "17:00")
duration = 30  # minutes

# Find the earliest meeting time
day, time_range = find_earliest_meeting_time(participants, days, work_hours, duration)

# Output the result
print(f"{day}: {time_range}")