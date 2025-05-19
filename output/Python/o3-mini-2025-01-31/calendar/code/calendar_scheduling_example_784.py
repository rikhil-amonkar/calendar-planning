from datetime import time

# Define meeting duration in minutes
MEETING_DURATION = 60

# Define work hours (start and end)
work_start = time(9, 0)
work_end = time(17, 0)

# Participant schedules (start_time, end_time) in minutes from midnight for simplicity
# We'll convert times to minutes from midnight (e.g., 9:00 -> 540)

def to_minutes(hour, minute):
    return hour * 60 + minute

# Convert work hours to minutes
work_start_minutes = to_minutes(9, 0)
work_end_minutes = to_minutes(17, 0)

# Blocked times for each participant in minutes:
# Judith's blocks: Monday: 12:00-12:30, Wednesday: 11:30-12:00
judith_blocks = {
    "Monday": [(to_minutes(12, 0), to_minutes(12, 30))],
    "Tuesday": [],  # No blocks Tuesday
    "Wednesday": [(to_minutes(11, 30), to_minutes(12, 0))]
}

# Timothy's blocks:
timothy_blocks = {
    "Monday": [
        (to_minutes(9, 30), to_minutes(10, 0)),
        (to_minutes(10, 30), to_minutes(11, 30)),
        (to_minutes(12, 30), to_minutes(14, 0)),
        (to_minutes(15, 30), to_minutes(17, 0))
    ],
    "Tuesday": [
        (to_minutes(9, 30), to_minutes(13, 0)),
        (to_minutes(13, 30), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(17, 0))
    ],
    "Wednesday": [
        (to_minutes(9, 0), to_minutes(9, 30)),
        (to_minutes(10, 30), to_minutes(11, 0)),
        (to_minutes(13, 30), to_minutes(14, 30)),
        (to_minutes(15, 0), to_minutes(15, 30)),
        (to_minutes(16, 0), to_minutes(16, 30))
    ]
}

# Preference constraints:
# Judith would like to avoid meetings on Monday and avoid before 12:00 on Wednesday.
# Hence, we will try to schedule on Tuesday or Wednesday after 12:00.
# Note: Tuesday does not appear to have a sufficient free block for one hour based on Timothy's schedule.

def is_slot_free(day, start, duration, blocks):
    end = start + duration
    # The meeting must lie completely within work hours.
    if start < work_start_minutes or end > work_end_minutes:
        return False
    # Check against all blocks in a given day.
    for block_start, block_end in blocks:
        # If the meeting overlaps with any blocked interval, it's not free.
        if not (end <= block_start or start >= block_end):
            return False
    return True

# We'll search for a valid meeting time among the days "Monday", "Tuesday", "Wednesday".
# Given Judith's preferences, we prefer Tuesday or Wednesday after 12:00.
days = ["Monday", "Tuesday", "Wednesday"]

meeting_day = None
meeting_start = None

for day in days:
    # Combined blocks for both participants for this day
    blocks = []
    blocks.extend(judith_blocks.get(day, []))
    blocks.extend(timothy_blocks.get(day, []))
    # Sort blocks for potential future use
    blocks.sort(key=lambda x: x[0])
    
    # Determine the earliest possible start time:
    earliest = work_start_minutes
    latest = work_end_minutes - MEETING_DURATION  # meeting must end by work_end
    
    # Apply preferences:
    if day == "Monday":
        # Judith prefers to avoid Monday meetings.
        continue
    if day == "Wednesday":
        # Judith prefers not to have meeting before 12:00 on Wednesday.
        earliest = max(earliest, to_minutes(12, 0))
    
    # Try every minute (could be optimized, but small range) for a meeting start time from earliest to latest.
    found = False
    for start in range(earliest, latest + 1):
        if is_slot_free(day, start, MEETING_DURATION, blocks):
            meeting_day = day
            meeting_start = start
            found = True
            break
    if found:
        break

if meeting_day and meeting_start is not None:
    # Convert meeting_start from minutes to HH:MM format.
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_total = meeting_start + MEETING_DURATION
    end_hour = end_total // 60
    end_minute = end_total % 60
    # Format time output
    time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(meeting_day)
    print(time_range)
else:
    print("No possible time slot found.")