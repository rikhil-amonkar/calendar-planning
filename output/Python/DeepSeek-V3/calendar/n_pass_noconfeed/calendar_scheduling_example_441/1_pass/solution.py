from typing import List, Dict, Tuple

def find_meeting_time(participants: Dict[str, List[Tuple[str, str]]], duration_minutes: int, work_hours: Tuple[str, str]) -> Tuple[str, str]:
    # Convert all time slots to minutes since 00:00 for easier comparison
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start, work_end = map(time_to_minutes, work_hours)
    busy_slots = []

    # Collect all busy slots from participants
    for person, meetings in participants.items():
        for start, end in meetings:
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_slots.append((start_min, end_min))

    # Sort all busy slots by start time
    busy_slots.sort()

    # Find free slots by checking gaps between busy slots and work hours
    free_slots = []
    prev_end = work_start

    for start, end in busy_slots:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    # Check the slot after the last busy slot until work_end
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Find the first free slot that can accommodate the meeting duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))

    return None

# Define participants and their busy slots
participants = {
    "Joan": [("11:30", "12:00"), ("14:30", "15:00")],
    "Megan": [("9:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
    "Austin": [],
    "Betty": [("9:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Judith": [("9:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
    "Terry": [("9:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Kathryn": [("9:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"), ("14:00", "16:00"), ("16:30", "17:00")]
}

# Meeting duration in minutes
duration = 30
work_hours = ("9:00", "17:00")

# Find the meeting time
meeting_time = find_meeting_time(participants, duration, work_hours)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print("Monday")
else:
    print("No suitable time found.")