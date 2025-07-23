from typing import List, Dict, Tuple

def schedule_meeting(
    participants: List[str],
    schedules: Dict[str, Dict[str, List[Tuple[str, str]]]],
    preferences: Dict[str, Dict[str, str]],
    work_hours: Tuple[str, str],
    meeting_duration: int,
    days: List[str]
) -> Tuple[str, str]:
    # Convert time string "HH:MM" to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to "HH:MM" format
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Parse work hours
    work_start, work_end = map(time_to_minutes, work_hours)
    
    # Iterate through each day and find available slots
    for day in days:
        # Check preferences
        skip_day = False
        for participant, pref in preferences.items():
            if pref.get("no_day") == day:
                skip_day = True
                break
            if pref.get("no_before") and day == pref.get("no_day"):
                no_before_time = time_to_minutes(pref["no_before"])
                # This will be handled in the slot checking
        if skip_day:
            continue

        # Collect all busy intervals for the day
        busy_intervals = []
        for participant in participants:
            for interval in schedules[participant].get(day, []):
                start, end = map(time_to_minutes, interval)
                busy_intervals.append((start, end))
        
        # Sort busy intervals by start time
        busy_intervals.sort()

        # Merge overlapping or adjacent busy intervals
        merged = []
        for start, end in busy_intervals:
            if not merged:
                merged.append([start, end])
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1][1] = max(end, last_end)
                else:
                    merged.append([start, end])

        # Find available slots between work hours and busy intervals
        available_slots = []
        prev_end = work_start

        for start, end in merged:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))

        # Check each available slot for meeting duration and preferences
        for slot_start, slot_end in available_slots:
            slot_duration = slot_end - slot_start
            if slot_duration >= meeting_duration:
                # Check time preferences
                valid_slot = True
                for participant, pref in preferences.items():
                    if pref.get("no_day") == day:
                        valid_slot = False
                        break
                    if pref.get("no_before") and day == pref.get("no_day"):
                        no_before_time = time_to_minutes(pref["no_before"])
                        if slot_start < no_before_time:
                            valid_slot = False
                            break
                if valid_slot:
                    return day, f"{minutes_to_time(slot_start)}:{minutes_to_time(slot_start + meeting_duration)}"

    return None, None

# Define participants
participants = ["Daniel", "Bradley"]

# Define schedules
schedules = {
    "Daniel": {
        "Monday": [("9:30", "10:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
        "Tuesday": [("11:00", "12:00"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Wednesday": [("9:00", "10:00"), ("14:00", "14:30")],
        "Thursday": [("10:30", "11:00"), ("12:00", "13:00"), ("14:30", "15:00"), ("15:30", "16:00")],
        "Friday": [("9:00", "9:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:30", "17:00")]
    },
    "Bradley": {
        "Monday": [("9:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:00", "15:00")],
        "Tuesday": [("10:30", "11:00"), ("12:00", "13:00"), ("13:30", "14:00"), ("15:30", "16:30")],
        "Wednesday": [("9:00", "10:00"), ("11:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")],
        "Thursday": [("9:00", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
        "Friday": [("9:00", "9:30"), ("10:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:30")]
    }
}

# Define preferences
preferences = {
    "Daniel": {"no_day": "Wednesday"},  # Would rather not meet on Wednesday or Thursday
    "Bradley": {"no_day": "Monday", "no_before": "12:00", "no_day_before": "Tuesday"}  # Do not want to meet on Monday, Tuesday before 12:00, or Friday
}

# Define work hours and meeting duration
work_hours = ("9:00", "17:00")
meeting_duration = 30  # minutes

# Define days to consider
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Schedule the meeting
day, time_range = schedule_meeting(participants, schedules, preferences, work_hours, meeting_duration, days)

# Output the result
if day and time_range:
    start_time, end_time = time_range.split(':')
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")