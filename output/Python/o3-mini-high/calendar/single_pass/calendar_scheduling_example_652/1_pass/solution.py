def time_to_minutes(t):
    """Converts time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time_str(m):
    """Converts minutes since midnight to time string 'HH:MM'."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a list of busy intervals (tuples of start, end in minutes) and
    the work period (work_start, work_end), return a list of free intervals.
    """
    free = []
    current = work_start
    # Sort the busy intervals by start time.
    for b_start, b_end in sorted(busy):
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2, meeting_duration):
    """
    Intersect two lists of intervals and return intervals
    that can accommodate a meeting of meeting_duration minutes.
    """
    intersections = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start_common = max(start1, start2)
            end_common = min(end1, end2)
            if end_common - start_common >= meeting_duration:
                intersections.append((start_common, end_common))
    # Sort intersections by start time.
    return sorted(intersections)

def main():
    meeting_duration = 30  # meeting duration in minutes

    # Define working hours in minutes (09:00 to 17:00).
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Schedules for each participant by day.
    schedule = {
        "Monday": {
            "Jesse": [
                (time_to_minutes("13:30"), time_to_minutes("14:00")),
                (time_to_minutes("14:30"), time_to_minutes("15:00"))
            ],
            "Lawrence": [
                (time_to_minutes("09:00"), time_to_minutes("17:00"))
            ]
        },
        "Tuesday": {
            "Jesse": [
                (time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("14:00"), time_to_minutes("15:00"))
            ],
            "Lawrence": [
                (time_to_minutes("09:30"), time_to_minutes("10:30")),
                (time_to_minutes("11:30"), time_to_minutes("12:30")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("14:30"), time_to_minutes("15:00")),
                (time_to_minutes("15:30"), time_to_minutes("16:30"))
            ]
        }
    }

    # Lawrence cannot meet on Tuesday after 16:30.
    # So for Tuesday, adjust his work day end time.
    lawrence_work_end = {
        "Monday": work_end,
        "Tuesday": time_to_minutes("16:30")
    }

    meeting_day = None
    meeting_start_time = None

    # Check each possible day (Monday, then Tuesday)
    for day in ["Monday", "Tuesday"]:
        # Compute free times for Jesse.
        jesse_busy = schedule[day]["Jesse"]
        jesse_free = get_free_intervals(jesse_busy, work_start, work_end)

        # Compute free times for Lawrence.
        lawrence_busy = schedule[day]["Lawrence"]
        # For Tuesday, use adjusted end time.
        lawrence_free = get_free_intervals(lawrence_busy, work_start, lawrence_work_end[day])

        # Find common free intervals that can host a meeting of required duration.
        common = intersect_intervals(jesse_free, lawrence_free, meeting_duration)
        if common:
            # Choose the earliest available time slot; schedule at the start of that interval.
            meeting_start_time = common[0][0]
            meeting_day = day
            break

    if meeting_day and meeting_start_time is not None:
        meeting_end_time = meeting_start_time + meeting_duration
        # Format output as HH:MM:HH:MM and day.
        time_range = f"{minutes_to_time_str(meeting_start_time)}:{minutes_to_time_str(meeting_end_time)}"
        print(f"{time_range} {meeting_day}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()