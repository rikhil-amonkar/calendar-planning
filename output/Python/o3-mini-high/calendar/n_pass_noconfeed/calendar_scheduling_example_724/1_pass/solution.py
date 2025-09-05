def time_to_minutes(t):
    # Converts a time string "HH:MM" into minutes past midnight.
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Converts minutes back into a time string "HH:MM"
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals (as tuples of minutes) and working hours,
    returns a list of free intervals within the working day.
    """
    free_intervals = []
    current = work_start
    for b_start, b_end in sorted(busy_intervals, key=lambda x: x[0]):
        if current < b_start:
            free_intervals.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """
    Computes the intersection of two lists of intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_inter = max(start1, start2)
        end_inter = min(end1, end2)
        if start_inter < end_inter:
            intersections.append((start_inter, end_inter))
        # Move to next interval from the list that ends earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot():
    meeting_duration = 30  # meeting duration is 30 minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Define each participant's busy schedule (times in minutes).
    # NOTE: Tyler has no explicit meetings on Monday, but he prefers to avoid meetings before 16:00.
    # We model his Monday preference as a busy interval from 09:00 to 16:00.
    schedules = {
        "Monday": {
            "Tyler": [
                (time_to_minutes("09:00"), time_to_minutes("16:00"))  # Preference to avoid earlier meetings.
            ],
            "Ruth": [
                (time_to_minutes("09:00"), time_to_minutes("10:00")),
                (time_to_minutes("10:30"), time_to_minutes("12:00")),
                (time_to_minutes("12:30"), time_to_minutes("14:30")),
                (time_to_minutes("15:00"), time_to_minutes("16:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))
            ]
        },
        "Tuesday": {
            "Tyler": [
                (time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("14:30"), time_to_minutes("15:00"))
            ],
            "Ruth": [
                (time_to_minutes("09:00"), time_to_minutes("17:00"))
            ]
        },
        "Wednesday": {
            "Tyler": [
                (time_to_minutes("10:30"), time_to_minutes("11:00")),
                (time_to_minutes("12:30"), time_to_minutes("13:00")),
                (time_to_minutes("13:30"), time_to_minutes("14:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))
            ],
            "Ruth": [
                (time_to_minutes("09:00"), time_to_minutes("17:00"))
            ]
        }
    }
    
    # Try scheduling on Monday, Tuesday, or Wednesday in order.
    for day in ["Monday", "Tuesday", "Wednesday"]:
        # Compute free intervals for each participant.
        free_tyler = compute_free_intervals(schedules[day]["Tyler"], work_start, work_end)
        free_ruth = compute_free_intervals(schedules[day]["Ruth"], work_start, work_end)
        
        # Find the overlapping free intervals.
        common_free = intersect_intervals(free_tyler, free_ruth)
        
        # Look for an interval long enough for the meeting.
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                # Output in the format "HH:MM:HH:MM" along with the day.
                print(f"{start_str}:{end_str} {day}")
                return

find_meeting_slot()