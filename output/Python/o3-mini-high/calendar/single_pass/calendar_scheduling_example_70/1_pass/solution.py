def time_to_minutes(time_str):
    """Convert a time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to a time string 'HH:MM'."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, day_start, day_end):
    """
    Given a sorted list of busy intervals (tuples of start and end times in minutes)
    and the working day boundaries, compute the free intervals.
    """
    free = []
    current = day_start
    for start, end in sorted(busy):
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Compute the intersection of two lists of intervals.
    Each interval is a tuple of (start, end) in minutes.
    """
    i, j = 0, 0
    inter = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            inter.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return inter

# Working hours for Monday: 09:00 to 17:00
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 30  # minutes

# Define each participant's busy schedule (times in minutes)
# Denise: Busy from 12:00 to 12:30, and 15:30 to 16:00.
denise_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Angela: No meetings (completely free).
angela_busy = []

# Natalie: Busy from 09:00 to 11:30, 12:00 to 13:00, 14:00 to 14:30, 15:00 to 17:00.
natalie_busy = [
    (time_to_minutes("09:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]

# Calculate free intervals for each participant
denise_free = get_free_intervals(denise_busy, WORK_START, WORK_END)
angela_free = get_free_intervals(angela_busy, WORK_START, WORK_END)
natalie_free = get_free_intervals(natalie_busy, WORK_START, WORK_END)

# Find common free intervals among all participants
common_free = intersect_intervals(denise_free, angela_free)
common_free = intersect_intervals(common_free, natalie_free)

# Select the earliest slot that can accommodate the 30-minute meeting.
meeting_start, meeting_end = None, None
for start, end in common_free:
    if end - start >= MEETING_DURATION:
        meeting_start = start
        meeting_end = start + MEETING_DURATION
        break

if meeting_start is not None:
    # Format the meeting time in HH:MM:HH:MM format.
    meeting_time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day = "Monday"
    print(f"{day} {meeting_time_range}")
else:
    print("No available time slot for the meeting.")