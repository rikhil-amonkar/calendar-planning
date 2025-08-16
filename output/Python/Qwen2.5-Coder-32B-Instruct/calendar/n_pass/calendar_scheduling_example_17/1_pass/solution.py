from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, day_of_week, max_time):
    # Convert all times to minutes since start of the day for easier comparison
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours, minutes = divmod(minutes, 60)
        return f"{hours:02}:{minutes:02}"

    start_of_day = time_to_minutes("09:00")
    end_of_day = time_to_minutes(max_time)

    # Create a list of available slots for each person
    available_slots = []
    for person_schedule in schedules:
        slots = []
        current_start = start_of_day
        for event_start, event_end in person_schedule:
            event_start_minutes = time_to_minutes(event_start)
            event_end_minutes = time_to_minutes(event_end)
            if current_start < event_start_minutes:
                slots.append((current_start, event_start_minutes))
            current_start = max(current_start, event_end_minutes)
        if current_start < end_of_day:
            slots.append((current_start, end_of_day))
        available_slots.append(slots)

    # Find common available slots
    common_slots = available_slots[0]
    for slots in available_slots[1:]:
        new_common_slots = []
        for start1, end1 in common_slots:
            for start2, end2 in slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots

    # Find the first valid slot
    for start, end in common_slots:
        if end - start >= meeting_duration:
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + meeting_duration)
            return f"{meeting_start}:{meeting_end}", day_of_week

    return None, None

# Define schedules
margaret_schedule = [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "15:30")]
donna_schedule = [("14:30", "15:00"), ("16:00", "16:30")]
helen_schedule = [("09:00", "09:30"), ("10:00", "11:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")]

# Combine schedules
schedules = [margaret_schedule, donna_schedule, helen_schedule]

# Meeting details
meeting_duration = 30  # in minutes
day_of_week = "Monday"
max_time = "13:30"

# Find a suitable meeting time
meeting_time, day = find_meeting_time(schedules, meeting_duration, day_of_week, max_time)
print(f"{meeting_time}, {day}")