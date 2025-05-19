from datetime import datetime, timedelta

# Define time in minutes since midnight for convenience
def time_to_minutes(time_str):
    """Convert HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM formatted string."""
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Work hours and meeting duration in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Participant schedules represented as lists of (start, end) in minutes. 
# These intervals are blocked times.
schedules = {
    "Diane": [(time_to_minutes("09:30"), time_to_minutes("10:00")),
              (time_to_minutes("14:30"), time_to_minutes("15:00"))],
    "Jack": [(time_to_minutes("13:30"), time_to_minutes("14:00")),
             (time_to_minutes("14:30"), time_to_minutes("15:00"))],
    "Eugene": [(time_to_minutes("09:00"), time_to_minutes("10:00")),
               (time_to_minutes("10:30"), time_to_minutes("11:30")),
               (time_to_minutes("12:00"), time_to_minutes("14:30")),
               (time_to_minutes("15:00"), time_to_minutes("16:30"))],
    "Patricia": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
                 (time_to_minutes("11:00"), time_to_minutes("12:00")),
                 (time_to_minutes("12:30"), time_to_minutes("14:00")),
                 (time_to_minutes("15:00"), time_to_minutes("16:30"))]
}

def is_free(person, start, end):
    """
    Check if the person is free during the time interval [start, end).
    A person is free if the meeting interval does not overlap any blocked interval.
    """
    for block in schedules[person]:
        block_start, block_end = block
        # Overlap exists if meeting starts before block ends and meeting ends after block starts.
        if start < block_end and end > block_start:
            return False
    return True

def find_meeting_time():
    # We'll iterate through the work day in minute increments
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        # Check if the proposed interval fully fits in work hours.
        if end > work_end:
            continue
        
        # Check all participants
        if all(is_free(person, start, end) for person in schedules):
            return start, end
    return None

meeting = find_meeting_time()

if meeting:
    meeting_start, meeting_end = meeting
    # Format output as HH:MM:HH:MM
    time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day = "Monday"
    print(f"Proposed meeting time: {time_str} on {day}")
else:
    print("No suitable meeting time found.")