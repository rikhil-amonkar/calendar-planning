from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in HH:MM format to minutes since 9:00."""
    hh, mm = map(int, time_str.split(':'))
    return (hh - 9) * 60 + mm

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hh = 9 + minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def find_meeting_time(
    participants: List[Dict[str, List[Tuple[str, str]]]],
    work_hours: Tuple[str, str],
    meeting_duration: int,
    days: List[str],
    preferences: Dict[str, List[Tuple[str, str]]]
) -> Tuple[str, str]:
    """Find a suitable meeting time based on constraints."""
    start_work, end_work = work_hours
    work_start = parse_time(start_work)
    work_end = parse_time(end_work)
    duration = meeting_duration

    # Initialize available slots for each day
    available_slots = {}
    for day in days:
        available_slots[day] = [(work_start, work_end)]

    # Apply each participant's busy slots
    for participant in participants:
        for day, busy_slots in participant.items():
            if day not in available_slots:
                continue
            current_slots = available_slots[day]
            new_slots = []
            for busy_start, busy_end in busy_slots:
                busy_start_min = parse_time(busy_start)
                busy_end_min = parse_time(busy_end)
                for slot_start, slot_end in current_slots:
                    if busy_end_min <= slot_start or busy_start_min >= slot_end:
                        new_slots.append((slot_start, slot_end))
                    else:
                        if slot_start < busy_start_min:
                            new_slots.append((slot_start, busy_start_min))
                        if busy_end_min < slot_end:
                            new_slots.append((busy_end_min, slot_end))
                current_slots = new_slots
                new_slots = []
            available_slots[day] = current_slots

    # Apply preferences (avoid certain times)
    for day, avoid_slots in preferences.items():
        if day not in available_slots:
            continue
        current_slots = available_slots[day]
        new_slots = []
        for avoid_start, avoid_end in avoid_slots:
            avoid_start_min = parse_time(avoid_start)
            avoid_end_min = parse_time(avoid_end)
            for slot_start, slot_end in current_slots:
                if avoid_end_min <= slot_start or avoid_start_min >= slot_end:
                    new_slots.append((slot_start, slot_end))
                else:
                    if slot_start < avoid_start_min:
                        new_slots.append((slot_start, avoid_start_min))
                    if avoid_end_min < slot_end:
                        new_slots.append((avoid_end_min, slot_end))
            current_slots = new_slots
            new_slots = []
        available_slots[day] = current_slots

    # Find the first available slot that fits the duration
    for day in days:
        for slot_start, slot_end in available_slots.get(day, []):
            if slot_end - slot_start >= duration:
                meeting_start = slot_start
                meeting_end = meeting_start + duration
                return day, f"{format_time(meeting_start)}:{format_time(meeting_end)}"

    return None, None

# Define participants' busy times
tyler_busy = {
    "Tuesday": [("9:00", "9:30"), ("14:30", "15:00")],
    "Wednesday": [("10:30", "11:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")]
}

ruth_busy = {
    "Monday": [("9:00", "10:00"), ("10:30", "12:00"), ("12:30", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
    "Tuesday": [("9:00", "17:00")],
    "Wednesday": [("9:00", "17:00")]
}

# Define preferences (Tyler wants to avoid Monday before 16:00)
preferences = {
    "Monday": [("9:00", "16:00")]
}

# Define meeting parameters
work_hours = ("9:00", "17:00")
meeting_duration = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday"]

# Find meeting time
day, time_range = find_meeting_time(
    participants=[tyler_busy, ruth_busy],
    work_hours=work_hours,
    meeting_duration=meeting_duration,
    days=days,
    preferences=preferences
)

# Output the result
print(f"{day}: {time_range}")