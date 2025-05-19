import datetime

# Helper function to convert HH:MM string to minutes since midnight
def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

# Helper function to convert minutes since midnight to HH:MM string
def minutes_to_time(m):
    return f"{m//60:02d}:{m % 60:02d}"

# Function to check if a given time slot [start, end) conflicts with any busy intervals
def is_free(start, duration, busy_intervals):
    end = start + duration
    for interval in busy_intervals:
        busy_start, busy_end = interval
        # If meeting overlaps with a busy interval: start < busy_end and busy_start < end
        if start < busy_end and busy_start < end:
            return False
    return True

# Define meeting parameters
meeting_duration = 30  # in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Busy schedules for participants in minutes.
# Times are given in minutes from midnight.
# Note: Larry is available all day, so his busy list is empty.
# Samuel's busy intervals are provided for each day.
busy_schedules = {
    "Monday": [
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("12:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Wednesday": [
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00"))
    ]
}

# The order of day preference: Monday, then Tuesday, then Wednesday.
# Larry prefers not to meet on Wednesday and Samuel prefers avoiding Tuesday,
# so we choose the earliest available option considering these preferences.
preferred_days = ["Monday", "Tuesday", "Wednesday"]

meeting_day = None
meeting_start = None

# Iterate over the preferred days
for day in preferred_days:
    # Use Samuel's busy schedule for that day.
    busy_intervals = busy_schedules.get(day, [])
    
    # Try to find a slot between work_start and work_end - meeting_duration
    slot_found = False
    for start in range(work_start, work_end - meeting_duration + 1):
        if is_free(start, meeting_duration, busy_intervals):
            meeting_day = day
            meeting_start = start
            slot_found = True
            break
    if slot_found:
        break

if meeting_day and meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    # Format output as HH:MM:HH:MM and day of the week.
    meeting_time_formatted = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"Meeting scheduled on {meeting_day} at {meeting_time_formatted}")
else:
    print("No available slot found.")