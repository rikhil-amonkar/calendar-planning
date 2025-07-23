from typing import List, Dict, Tuple
import datetime

def find_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    work_hours: Tuple[str, str],
    meeting_duration: int,
    days: List[str],
    preferences: Dict[str, List[str]] = None
) -> Tuple[str, str]:
    """
    Finds a suitable meeting time based on participants' schedules and constraints.

    Args:
        participants: Dictionary with participant names as keys and their schedules as values.
                      Schedules are dictionaries with days as keys and lists of time blocks as values.
        work_hours: Tuple representing work hours in 'HH:MM' format (e.g., ('09:00', '17:00')).
        meeting_duration: Duration of the meeting in minutes.
        days: List of days to consider (e.g., ['Monday', 'Tuesday', 'Wednesday']).
        preferences: Dictionary with participant names as keys and their day preferences as values.

    Returns:
        A tuple containing the day and time range in 'HH:MM-HH:MM' format.
    """
    # Convert work hours to minutes since midnight
    work_start = convert_time_to_minutes(work_hours[0])
    work_end = convert_time_to_minutes(work_hours[1])

    # Iterate through each day in order
    for day in days:
        # Skip if day is not preferred by any participant
        if preferences:
            skip_day = False
            for participant, pref_days in preferences.items():
                if day in pref_days:
                    skip_day = True
                    break
            if skip_day:
                continue

        # Collect all busy intervals for the day
        busy_intervals = []
        for participant, schedule in participants.items():
            if day in schedule:
                for block in schedule[day]:
                    start = convert_time_to_minutes(block[0])
                    end = convert_time_to_minutes(block[1])
                    busy_intervals.append((start, end))

        # Add constraints for Sandra on Monday after 16:00
        if day == 'Monday':
            busy_intervals.append((convert_time_to_minutes('16:00'), work_end))

        # Sort busy intervals by start time
        busy_intervals.sort()

        # Find available slots
        available_slots = []
        prev_end = work_start

        for start, end in busy_intervals:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)

        # Check after last busy interval
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))

        # Find the first available slot that fits the meeting duration
        for slot in available_slots:
            slot_duration = slot[1] - slot[0]
            if slot_duration >= meeting_duration:
                meeting_start = slot[0]
                meeting_end = meeting_start + meeting_duration
                return (
                    day,
                    f"{convert_minutes_to_time(meeting_start)}:{convert_minutes_to_time(meeting_end)}"
                )

    return None

def convert_time_to_minutes(time_str: str) -> int:
    """Converts time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_minutes_to_time(minutes: int) -> str:
    """Converts minutes since midnight to 'HH:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Define participants' schedules
participants = {
    'Susan': {
        'Monday': [('12:30', '13:00'), ('13:30', '14:00')],
        'Tuesday': [('11:30', '12:00')],
        'Wednesday': [('09:30', '10:30'), ('14:00', '14:30'), ('15:30', '16:30')],
    },
    'Sandra': {
        'Monday': [('09:00', '13:00'), ('14:00', '15:00'), ('16:00', '16:30')],
        'Tuesday': [('09:00', '09:30'), ('10:30', '12:00'), ('12:30', '13:30'), ('14:00', '14:30'), ('16:00', '17:00')],
        'Wednesday': [('09:00', '11:30'), ('12:00', '12:30'), ('13:00', '17:00')],
    }
}

# Define constraints and preferences
work_hours = ('09:00', '17:00')
meeting_duration = 30  # minutes
days = ['Monday', 'Tuesday', 'Wednesday']
preferences = {
    'Susan': ['Tuesday'],
}

# Find the meeting time
result = find_meeting_time(participants, work_hours, meeting_duration, days, preferences)
if result:
    day, time_range = result
    start_time, end_time = time_range.split(':')
    print(f"{day}: {start_time}-{end_time}")
else:
    print("No suitable time found.")