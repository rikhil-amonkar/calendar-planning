from datetime import datetime, timedelta

# Define meeting parameters
meeting_duration = timedelta(minutes=30)
work_day_start = datetime.strptime("09:00", "%H:%M")
work_day_end = datetime.strptime("17:00", "%H:%M")
day_of_week = "Monday"

# Define Samuel's blocked time intervals (start, end)
# These intervals are within the work day
blocked_intervals = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
    (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
]

def is_available(candidate_start):
    candidate_end = candidate_start + meeting_duration
    # Check if the candidate meeting time is within working hours
    if candidate_start < work_day_start or candidate_end > work_day_end:
        return False
    # Check against all blocked intervals for overlaps
    for block_start, block_end in blocked_intervals:
        # Overlap occurs if candidate_start is before block_end and candidate_end is after block_start.
        if candidate_start < block_end and candidate_end > block_start:
            return False
    return True

# Start searching from the beginning of the day until the end of the day minus meeting duration
candidate_time = work_day_start
proposed_time = None

while candidate_time + meeting_duration <= work_day_end:
    if is_available(candidate_time):
        proposed_time = candidate_time
        break
    candidate_time += timedelta(minutes=1)

if proposed_time:
    proposed_end = proposed_time + meeting_duration
    # Format output as HH:MM:HH:MM along with day of the week.
    meeting_time_str = f"{proposed_time.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}"
    print(meeting_time_str)
    print(day_of_week)
else:
    print("No available meeting time found within the given constraints.")