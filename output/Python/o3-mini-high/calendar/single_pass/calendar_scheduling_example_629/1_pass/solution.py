def time_to_minutes(time_str):
    """Converts a time string HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to a time string HH:MM."""
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a list of busy intervals (start, end) in minutes (sorted by start),
    returns a list of available (free) intervals within the work hours.
    """
    free = []
    current = work_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def adjust_intervals_for_constraint(intervals, constraint_start):
    """
    For a given list of intervals, adjust any intervals so that
    the start is not before the constraint_start.
    """
    adjusted = []
    for start, end in intervals:
        if end <= constraint_start:
            continue
        if start < constraint_start:
            start = constraint_start
        adjusted.append((start, end))
    return adjusted

def intersect_intervals(intervals1, intervals2, duration):
    """
    Finds intersections between two lists of intervals.
    Only returns intersections that are at least 'duration' minutes long.
    """
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start >= duration:
                intersections.append((start, end))
    return intersections

def main():
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Define busy schedules for each participant on Monday and Tuesday.
    # Times are given as strings in HH:MM format and converted to minutes.
    schedule = {
        "Monday": {
            "Margaret": [
                (time_to_minutes("10:30"), time_to_minutes("11:00")),
                (time_to_minutes("11:30"), time_to_minutes("12:00")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("15:00"), time_to_minutes("17:00"))
            ],
            "Alexis": [
                (time_to_minutes("09:30"), time_to_minutes("11:30")),
                (time_to_minutes("12:30"), time_to_minutes("13:00")),
                (time_to_minutes("14:00"), time_to_minutes("17:00"))
            ]
        },
        "Tuesday": {
            "Margaret": [
                (time_to_minutes("12:00"), time_to_minutes("12:30"))
            ],
            "Alexis": [
                (time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("10:00"), time_to_minutes("10:30")),
                (time_to_minutes("14:00"), time_to_minutes("16:30"))
            ]
        }
    }

    # Additional constraints:
    # 1. Margaret does not want to meet on Monday.
    # 2. On Tuesday, Margaret does not want to meet before 14:30.
    #
    # Thus, the meeting must be scheduled on Tuesday and not start before 14:30.
    day = "Tuesday"
    marg_constraint_start = time_to_minutes("14:30")

    # Get free intervals for each participant on Tuesday.
    marg_busy = schedule[day]["Margaret"]
    alexis_busy = schedule[day]["Alexis"]

    marg_free = get_free_intervals(marg_busy, work_start, work_end)
    alexis_free = get_free_intervals(alexis_busy, work_start, work_end)

    # Apply Margaret's Tuesday constraint: remove any free time before 14:30.
    marg_free = adjust_intervals_for_constraint(marg_free, marg_constraint_start)

    # Find overlapping free intervals where a meeting can be scheduled.
    possible_slots = intersect_intervals(marg_free, alexis_free, meeting_duration)

    if not possible_slots:
        print("No available meeting time found.")
        return

    # Choose the earliest possible meeting slot.
    meeting_start = min(possible_slots, key=lambda x: x[0])[0]
    meeting_end = meeting_start + meeting_duration

    # Format the meeting time as HH:MM:HH:MM.
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"

    # Output the day and the meeting time range.
    print(day, meeting_time_str)

if __name__ == "__main__":
    main()