from datetime import datetime, timedelta

# Define meeting duration in minutes
meeting_duration = timedelta(minutes=30)

# Work hours: 9:00 to 17:00
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy intervals for each participant (for Monday and Tuesday)
# We'll represent an interval as a tuple (start_time, end_time)
# Note: Only Monday busy intervals for Doris matter (Tuesday is completely busy for Doris)

# Jean's busy intervals (none on Monday, but Tuesday has busy times)
jean_busy = {
    "Monday": [],  
    "Tuesday": [
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ]
}

# Doris's busy intervals
doris_busy = {
    "Monday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Doris's preference: would rather not meet on Monday after 14:00.
# So on Monday, any meeting must finish by 14:00.

def invert_busy_times(busy, day_start, day_end):
    """Return the free intervals given the busy intervals within the day."""
    free = []
    current_start = day_start
    for start, end in sorted(busy):
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < day_end:
        free.append((current_start, day_end))
    return free

def find_slot(free_intervals, meeting_duration, latest_end=None):
    """
    Find the first available slot within free intervals that can
    accommodate the meeting_duration. If latest_end is provided, the meeting must finish before or at latest_end.
    """
    for start, end in free_intervals:
        # If there's a constraint on the latest finish time, adjust the interval.
        if latest_end is not None and end > latest_end:
            end = min(end, latest_end)
        if end - start >= meeting_duration:
            return start, start + meeting_duration
    return None

# Function to get overall free intervals for all participants (intersection of their free slots)
def intersect_intervals(intervals_list):
    """
    intervals_list: list of lists, each containing free intervals (tuples)
    Returns the intersection of these intervals.
    """
    if not intervals_list:
        return []
    # Start by taking the free intervals of the first participant.
    result = intervals_list[0]
    for other in intervals_list[1:]:
        new_result = []
        for (start1, end1) in result:
            for (start2, end2) in other:
                # Find overlap
                start_overlap = max(start1, start2)
                end_overlap = min(end1, end2)
                if start_overlap < end_overlap:
                    new_result.append((start_overlap, end_overlap))
        result = new_result
    return result

# Store work day free intervals for Jean and Doris on both days
available_days = ["Monday", "Tuesday"]
meeting_proposal = None
proposal_day = None

for day in available_days:
    # For Jean, free time is the work hours minus his busy intervals for that day
    jean_free = invert_busy_times(jean_busy.get(day, []), work_start, work_end)
    # For Doris, free time is the work hours minus her busy intervals for that day
    doris_free = invert_busy_times(doris_busy.get(day, []), work_start, work_end)
    
    # Consider Doris's preference: on Monday, do not schedule after 14:00.
    latest_end = None
    if day == "Monday":
        # Meeting must end by 14:00
        latest_end = datetime.strptime("14:00", "%H:%M")
    
    # Intersection of free intervals for both participants
    combined_free = intersect_intervals([jean_free, doris_free])
    
    # If there's a preference for latest meeting end, trim intervals accordingly.
    if latest_end is not None:
        trimmed = []
        for s, e in combined_free:
            if s >= latest_end:
                continue
            trimmed.append((s, min(e, latest_end)))
        combined_free = trimmed

    slot = find_slot(combined_free, meeting_duration)
    if slot is not None:
        meeting_proposal = slot
        proposal_day = day
        break

if meeting_proposal:
    start, end = meeting_proposal
    meeting_time = f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}"
    print(meeting_time, proposal_day)
else:
    print("No available slot found.")