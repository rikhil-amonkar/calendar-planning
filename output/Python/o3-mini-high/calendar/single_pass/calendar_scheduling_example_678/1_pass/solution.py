def minutes_to_time_str(minutes):
    """Convert minutes since midnight into HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a sorted list of busy intervals and work hours,
    return the list of free intervals as (start, end) in minutes.
    """
    free = []
    if not busy:
        return [(work_start, work_end)]
    # Check time before the first busy interval
    if work_start < busy[0][0]:
        free.append((work_start, busy[0][0]))
    # Check gaps between busy intervals
    for i in range(len(busy)-1):
        current_end = busy[i][1]
        next_start = busy[i+1][0]
        if current_end < next_start:
            free.append((current_end, next_start))
    # Check time after the last busy interval
    if busy[-1][1] < work_end:
        free.append((busy[-1][1], work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, return the list of their intersections.
    Each interval is a tuple (start, end) in minutes.
    """
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Get the overlap
        start_common = max(start1, start2)
        end_common = min(end1, end2)
        if start_common < end_common:
            intersections.append((start_common, end_common))
        # Move to the next interval in the list that finishes first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot():
    meeting_duration = 60  # Duration of the meeting in minutes (1 hour)
    work_start = 9 * 60    # 9:00 -> 540 minutes
    work_end = 17 * 60     # 17:00 -> 1020 minutes
    
    # Define busy schedules in minutes for each participant on Monday and Tuesday
    schedules = {
        "Monday": {
            "Russell": [(10 * 60 + 30, 11 * 60)],                # 10:30 - 11:00  -> (630, 660)
            "Alexander": [
                (9 * 60, 11 * 60 + 30),                           # 9:00 - 11:30   -> (540, 690)
                (12 * 60, 14 * 60 + 30),                          # 12:00 - 14:30  -> (720, 870)
                (15 * 60, 17 * 60)                                # 15:00 - 17:00  -> (900, 1020)
            ]
        },
        "Tuesday": {
            "Russell": [(13 * 60, 13 * 60 + 30)],                 # 13:00 - 13:30  -> (780, 810)
            "Alexander": [
                (9 * 60, 10 * 60),                                # 9:00 - 10:00   -> (540, 600)
                (13 * 60, 14 * 60),                               # 13:00 - 14:00  -> (780, 840)
                (15 * 60, 15 * 60 + 30),                          # 15:00 - 15:30  -> (900, 930)
                (16 * 60, 16 * 60 + 30)                           # 16:00 - 16:30  -> (960, 990)
            ]
        }
    }
    
    # Iterate over possible days (Monday, Tuesday)
    for day in ["Monday", "Tuesday"]:
        busy_russell = schedules[day]["Russell"]
        busy_alex = schedules[day]["Alexander"]

        # Compute free intervals within work hours
        free_russell = get_free_intervals(busy_russell, work_start, work_end)
        free_alex = get_free_intervals(busy_alex, work_start, work_end)

        # Apply Russell's preference on Tuesday: he would rather not meet before 13:30 (810 minutes)
        if day == "Tuesday":
            adjusted_free = []
            for interval in free_russell:
                start, end = interval
                # Only consider the part of the interval that is after 13:30
                if end > 810:
                    adjusted_free.append((max(start, 810), end))
            free_russell = adjusted_free

        # Calculate intersections of free intervals for both participants
        common_free = intersect_intervals(free_russell, free_alex)

        # Look for an interval that can accommodate the meeting duration
        for interval in common_free:
            start, end = interval
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                return day, meeting_start, meeting_end

    # A solution is guaranteed so this point should not be reached.
    return None, None, None

def main():
    day, meeting_start, meeting_end = find_meeting_slot()
    if day is not None:
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        # Output in format "Day HH:MM:HH:MM"
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()