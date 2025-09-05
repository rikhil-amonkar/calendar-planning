def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    # Sort and filter busy intervals to those that intersect with the work window.
    busy_sorted = sorted(busy_intervals)
    free = []
    current_start = work_start
    for b_start, b_end in busy_sorted:
        # Ignore busy intervals that end before work_start.
        if b_end <= work_start:
            continue
        # If the busy interval starts after our working window, break.
        if b_start >= work_end:
            break
        # Clamp busy times to the working period.
        b_start = max(b_start, work_start)
        b_end = min(b_end, work_end)
        if current_start < b_start:
            free.append((current_start, b_start))
        current_start = max(current_start, b_end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

# Meeting parameters
MEETING_DURATION = 30  # in minutes
WORK_START = "09:00"
WORK_END = "17:00"
DAY = "Monday"

# Convert working hours to minutes
work_start_minutes = time_to_minutes(WORK_START)
work_end_minutes = time_to_minutes(WORK_END)

# Participant schedules:
# Deborah is free the whole day
deborah_busy = []  # no busy intervals

# Albert's busy intervals on Monday
albert_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("15:00"), time_to_minutes("16:30"))
]

# Albert cannot meet after 11:00 - so his effective working window ends at 11:00.
albert_meeting_end = min(work_end_minutes, time_to_minutes("11:00"))

# Get free intervals within the working periods.
albert_free_intervals = get_free_intervals(work_start_minutes, albert_meeting_end, albert_busy)
deborah_free_intervals = [(work_start_minutes, work_end_minutes)]  # Entire day is free

# Find an intersection of free intervals that can accommodate a 30-minute meeting.
meeting_slot = None
for d_start, d_end in deborah_free_intervals:
    for a_start, a_end in albert_free_intervals:
        # The intersection between Deborah's and Albert's free interval
        start_possible = max(d_start, a_start)
        end_possible = min(d_end, a_end)
        if end_possible - start_possible >= MEETING_DURATION:
            meeting_slot = (start_possible, start_possible + MEETING_DURATION)
            break
    if meeting_slot:
        break

if meeting_slot:
    meeting_start = minutes_to_time(meeting_slot[0])
    meeting_end = minutes_to_time(meeting_slot[1])
    # Output in the format "DAY HH:MM:HH:MM"
    print(f"{DAY} {meeting_start}:{meeting_end}")
else:
    print("No available slot found.")