from datetime import timedelta, datetime

# Define working hours: 9 am to 5 pm in minutes since midnight
WORK_START = 9 * 60    # 540 minutes (09:00)
WORK_END = 17 * 60     # 1020 minutes (17:00)
MEETING_DURATION = 30  # in minutes

# Define calendars as dictionaries: each key is a day and value is a list of busy intervals (in minutes)
# Busy intervals are represented as tuples (start, end) in minutes from midnight.
# Days considered: Monday, Tuesday, Wednesday
calendars = {
    "Cheryl": {
        "Monday": [(9 * 60, 9 * 60 + 30),    # 09:00-09:30
                   (11 * 60 + 30, 13 * 60),  # 11:30-13:00
                   (15 * 60 + 30, 16 * 60)], # 15:30-16:00
        "Tuesday": [(15 * 60, 15 * 60 + 30)],  # 15:00-15:30
        # Cheryl cannot meet on Wednesday
    },
    "Kyle": {
        "Monday": [(9 * 60, 17 * 60)],         # 09:00-17:00 (entire day busy)
        "Tuesday": [(9 * 60 + 30, 17 * 60)],     # 09:30-17:00
        "Wednesday": [(9 * 60, 9 * 60 + 30),     # 09:00-09:30
                      (10 * 60, 13 * 60),         # 10:00-13:00
                      (13 * 60 + 30, 14 * 60),    # 13:30-14:00
                      (14 * 60 + 30, 17 * 60)]    # 14:30-17:00
    }
}

# Allowed days for the meeting
allowed_days = ["Monday", "Tuesday", "Wednesday"]

def get_free_intervals(busy_intervals, work_start=WORK_START, work_end=WORK_END):
    """Given a list of busy intervals, return the list of free intervals within work hours."""
    free_intervals = []
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    current_start = work_start

    for busy in busy_intervals:
        busy_start, busy_end = busy
        if busy_start > current_start:
            free_intervals.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    # Check if there's free time after the last busy interval until end of work day.
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """Given two lists of intervals, return the intersection intervals."""
    intersection = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # find the overlap between intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move the pointer for the interval which ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def minutes_to_time_str(minutes):
    """Convert minutes since midnight to HH:MM format with zero padded hours/minutes."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def schedule_meeting():
    # We have two participants to schedule: Cheryl and Kyle.
    participants = ["Cheryl", "Kyle"]
    
    # Try each allowed day, taking into account individual constraints
    for day in allowed_days:
        # Skip if Cheryl can't meet on Wednesday.
        if day == "Wednesday" and "Cheryl" in calendars and day not in calendars["Cheryl"]:
            continue  # Cheryl has no available data for Wednesday due to constraint
        
        # Build free intervals for each participant for the given day.
        participant_free = []
        for person in participants:
            # Get busy intervals within working hours; if no entry for a day, assume free all day.
            busy = calendars.get(person, {}).get(day, [])
            free = get_free_intervals(busy)
            participant_free.append(free)
        
        # Compute the common free intervals across all participants.
        common_intervals = participant_free[0]
        for i in range(1, len(participant_free)):
            common_intervals = intersect_intervals(common_intervals, participant_free[i])
        
        # Check if any common interval can accommodate the meeting duration.
        for interval in common_intervals:
            start, end = interval
            if end - start >= MEETING_DURATION:
                meeting_start = start
                meeting_end = start + MEETING_DURATION
                # Format the meeting time in HH:MM:HH:MM and output day.
                meeting_time_str = f"{minutes_to_time_str(meeting_start)}:{minutes_to_time_str(meeting_end)}"
                print(f"Day: {day}, Time: {meeting_time_str}")
                return

# Run scheduling function
schedule_meeting()