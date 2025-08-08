def time_to_minutes(t):
    """Convert HH:MM time string to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM time string."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Given a list of busy intervals (in minutes), return free intervals within work hours."""
    # Sort busy intervals by start time.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        if end > current:
            current = end
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
    result = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start > 0:
                result.append((start, end))
    return result

def main():
    # Define work hours and meeting duration (in minutes)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30
    day = "Monday"
    
    # Define each participant's busy schedule for Monday in HH:MM format.
    schedules = {
        "Joe": [("09:30", "10:00"), ("10:30", "11:00")],
        "Keith": [("11:30", "12:00"), ("15:00", "15:30")],
        "Patricia": [("09:00", "09:30"), ("13:00", "13:30")],
        "Nancy": [("09:00", "11:00"), ("11:30", "16:30")],
        "Pamela": [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"),
                   ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
    }
    
    # Convert all busy intervals to minutes.
    busy_minutes = {}
    for person, intervals in schedules.items():
        busy_minutes[person] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]
    
    # Calculate free intervals for each participant within work hours.
    free_intervals = {}
    for person, busy in busy_minutes.items():
        free_intervals[person] = get_free_intervals(busy, work_start, work_end)
    
    # Determine the common free intervals among all participants.
    persons = list(schedules.keys())
    # Start with the free intervals of the first participant.
    common_free = free_intervals[persons[0]]
    for person in persons[1:]:
        common_free = intersect_intervals(common_free, free_intervals[person])
    
    # Find the first common free interval that can accommodate the meeting duration.
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is not None:
        meeting_end = meeting_start + meeting_duration
        # Format the meeting time as HH:MM:HH:MM.
        meeting_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
        # Output the day and the meeting time.
        print(f"{day} {meeting_time}")
    else:
        print("No common time slot available.")

if __name__ == "__main__":
    main()