def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time_str(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

# Workday settings for Monday
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # duration in minutes
meeting_day = "Monday"

# Busy intervals for each participant (in minutes)
busy_schedules = {
    "Olivia": [
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
    "Anna": [
        # Anna has no meetings
    ],
    "Virginia": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
    "Paul": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ]
}

# Function to check if a meeting slot conflicts with any busy interval
def is_conflict(start, end, busy_intervals):
    for bstart, bend in busy_intervals:
        # Check if meeting [start, end] overlaps with busy interval (allowing touching boundaries)
        if start < bend and end > bstart:
            return True
    return False

# Search for a valid meeting slot within work hours
found_slot = False
for start in range(work_start, work_end - meeting_duration + 1):
    meeting_end = start + meeting_duration
    conflict_found = False
    for person, intervals in busy_schedules.items():
        if is_conflict(start, meeting_end, intervals):
            conflict_found = True
            break
    if not conflict_found:
        # Slot found, output in the required format
        start_str = minutes_to_time_str(start)
        end_str = minutes_to_time_str(meeting_end)
        print(f"{meeting_day} {start_str}:{end_str}")
        found_slot = True
        break

if not found_slot:
    print("No available time slot found.")