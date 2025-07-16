from typing import List, Dict, Tuple

def find_meeting_time(participants: Dict[str, List[Tuple[str, str]]], 
                     work_hours: Tuple[str, str], 
                     duration_minutes: int, 
                     day: str) -> Tuple[str, str, str]:
    # Convert all time strings to minutes since 9:00 (start of work hours)
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 9 * 60  # Subtract 9:00 (540 minutes) to normalize

    def minutes_to_time(minutes: int) -> str:
        total_minutes = 9 * 60 + minutes  # Add back 9:00
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration = duration_minutes

    # Collect all busy intervals for each participant
    busy_intervals = []
    for participant, intervals in participants.items():
        for start, end in intervals:
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals.append((start_min, end_min))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Find the earliest available slot
    prev_end = work_start_min
    for start, end in merged:
        if start > prev_end and start - prev_end >= duration:
            # Found a slot
            meeting_start = prev_end
            meeting_end = meeting_start + duration
            return (day, 
                    minutes_to_time(meeting_start), 
                    minutes_to_time(meeting_end))
        prev_end = max(prev_end, end)

    # Check after the last busy interval
    if work_end_min - prev_end >= duration:
        meeting_start = prev_end
        meeting_end = meeting_start + duration
        return (day, 
                minutes_to_time(meeting_start), 
                minutes_to_time(meeting_end))

    return (None, None, None)

# Input data
participants = {
    "Denise": [("12:00", "12:30"), ("15:30", "16:00")],
    "Angela": [],
    "Natalie": [("9:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
}
work_hours = ("9:00", "17:00")
duration_minutes = 30
day = "Monday"

# Find the meeting time
day, start_time, end_time = find_meeting_time(participants, work_hours, duration_minutes, day)

# Output the result
print(f"{day}:{start_time}:{end_time}")