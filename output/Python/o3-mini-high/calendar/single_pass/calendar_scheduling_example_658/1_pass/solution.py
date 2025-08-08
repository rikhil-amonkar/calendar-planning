def minutes_to_time(m):
    """Convert minutes since midnight to a HH:MM string."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_slots(work_start, work_end, busy_intervals):
    """
    Given working hours and a sorted list of busy intervals,
    return a list of free intervals within the working day.
    Each interval is a tuple (start, end) in minutes.
    """
    free = []
    current = work_start
    for bstart, bend in sorted(busy_intervals):
        if bstart > current:
            free.append((current, bstart))
        current = max(current, bend)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2, meeting_duration):
    """
    Compute the intersections between two lists of intervals.
    Only returns intervals with a span at least equal to meeting_duration.
    """
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start >= meeting_duration:
                intersections.append((start, end))
    return intersections

def find_meeting_time():
    meeting_duration = 30  # meeting duration in minutes
    # Working hours: from 09:00 (540 minutes) to 17:00 (1020 minutes)
    work_start = 9 * 60
    work_end = 17 * 60

    # Busy schedules (times in minutes)
    schedules = {
        "Monday": {
            "Shirley": [(10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (16 * 60, 16 * 60 + 30)],
            # Albert is busy all day Monday: 09:00 - 17:00
            "Albert": [(work_start, work_end)]
        },
        "Tuesday": {
            "Shirley": [(9 * 60 + 30, 10 * 60)],  # Busy from 09:30 to 10:00
            "Albert": [
                (9 * 60 + 30, 11 * 60),      # 09:30 to 11:00
                (11 * 60 + 30, 12 * 60 + 30),# 11:30 to 12:30
                (13 * 60, 16 * 60),          # 13:00 to 16:00
                (16 * 60 + 30, work_end)     # 16:30 to 17:00
            ]
        }
    }
    
    # Preference: On Tuesday, Shirley prefers not to meet after 10:30.
    # For a 30-minute meeting, we require the meeting to start by 10:00.
    latest_tuesday_start = 10 * 60  # 10:00 in minutes

    # Check each day
    for day in ["Monday", "Tuesday"]:
        free_shirley = get_free_slots(work_start, work_end, schedules[day]["Shirley"])
        free_albert = get_free_slots(work_start, work_end, schedules[day]["Albert"])
        
        # Find common free intervals
        common_free = intersect_intervals(free_shirley, free_albert, meeting_duration)
        # Sort by start time
        common_free.sort(key=lambda x: x[0])
        
        for interval in common_free:
            start, end = interval
            # Ensure the interval has enough time for the meeting
            if end - start >= meeting_duration:
                candidate_start = start
                candidate_end = start + meeting_duration
                # Apply Tuesday's preference if applicable
                if day == "Tuesday" and candidate_start > latest_tuesday_start:
                    continue
                return day, candidate_start, candidate_end

    return None, None, None

if __name__ == "__main__":
    day, start, end = find_meeting_time()
    if day is not None:
        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)
        # Output in the specified format: Day and the time range HH:MM:HH:MM
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")