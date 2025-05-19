from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Converts time string HH:MM to minutes from midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes from midnight to time string HH:MM."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define working hours and meeting duration (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Define blocked intervals for each participant in minutes (start, end)
# Michael: 9:30 to 10:30, 15:00 to 15:30, 16:00 to 16:30
michael_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Eric's calendar is free, so no blocks
eric_busy = []

# Arthur: 9:00 to 12:00, 13:00 to 15:00, 15:30 to 16:00, 16:30 to 17:00
arthur_busy = [
    (time_to_minutes("09:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Combine the busy intervals for all participants
all_busy = michael_busy + eric_busy + arthur_busy

def is_time_slot_available(start, duration, busy_intervals):
    """Check if the time slot starting at 'start' with 'duration' minutes is free
       from any conflicts in the list of busy intervals."""
    end = start + duration
    for busy_start, busy_end in busy_intervals:
        # if the meeting overlaps with any busy interval
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

# Find the first available slot from work_start to work_end - meeting_duration
slot_found = None
for start in range(work_start, work_end - meeting_duration + 1):
    if is_time_slot_available(start, meeting_duration, all_busy):
        slot_found = (start, start + meeting_duration)
        break

if slot_found:
    start_time_str = minutes_to_time(slot_found[0])
    end_time_str = minutes_to_time(slot_found[1])
    meeting_day = "Monday"
    # Output in the format: HH:MM:HH:MM and day of the week.
    print(f"{meeting_day} {start_time_str}:{end_time_str}")
else:
    print("No available slot found.")