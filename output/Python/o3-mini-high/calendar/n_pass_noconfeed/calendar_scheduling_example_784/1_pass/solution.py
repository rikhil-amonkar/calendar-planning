def parse_time(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    """Convert minutes since midnight to HH:MM string (zero-padded)."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (each as (start_str, end_str)),
    return a list of free intervals in (start_minute, end_minute) within work hours.
    """
    # Convert busy intervals to minutes and sort them
    busy = sorted([(parse_time(start), parse_time(end)) for start, end in busy_intervals])
    free = []
    current = work_start
    for b_start, b_end in busy:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersect two lists of intervals. Each interval is a tuple (start, end)."""
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # Find overlap
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersection.append((start, end))
        # Move to next interval in the list that ends first
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersection

def find_meeting_slot(common_intervals, duration, day, extra_min_start=None):
    """
    Given a list of common free intervals and the meeting duration in minutes,
    return a tuple (meeting_start, meeting_end) if a slot is found.
    If extra_min_start is provided, the meeting start must be no earlier than that.
    """
    for start, end in common_intervals:
        candidate_start = start
        if extra_min_start is not None:
            candidate_start = max(start, extra_min_start)
        if candidate_start + duration <= end:
            return candidate_start, candidate_start + duration
    return None

def main():
    # Define work hours (in minutes)
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    meeting_duration = 60  # in minutes

    # Participants' busy schedules (times are strings "HH:MM")
    schedules = {
        "Monday": {
            "Judith": [("12:00", "12:30")],
            "Timothy": [("09:30", "10:00"), ("10:30", "11:30"), ("12:30", "14:00"), ("15:30", "17:00")]
        },
        "Tuesday": {
            "Judith": [],
            "Timothy": [("09:30", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")]
        },
        "Wednesday": {
            "Judith": [("11:30", "12:00")],
            "Timothy": [("09:00", "09:30"), ("10:30", "11:00"), ("13:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")]
        }
    }

    # We need to choose a day among Monday, Tuesday, Wednesday.
    # Judith prefers to avoid Monday if possible.
    # Also, on Wednesday, she would like to avoid meetings before 12:00.
    # Therefore, we will try days in this order: Tuesday, Wednesday, then Monday.
    preferred_days = ["Tuesday", "Wednesday", "Monday"]

    meeting_day = None
    meeting_time = None

    for day in preferred_days:
        # Compute free intervals for each participant on this day
        judith_busy = schedules[day].get("Judith", [])
        timothy_busy = schedules[day].get("Timothy", [])

        judith_free = get_free_intervals(judith_busy, work_start, work_end)
        timothy_free = get_free_intervals(timothy_busy, work_start, work_end)

        # Compute common free intervals
        common_free = intersect_intervals(judith_free, timothy_free)
        
        # For Wednesday, enforce that meeting start is not before 12:00.
        extra_min_start = None
        if day == "Wednesday":
            extra_min_start = parse_time("12:00")
        
        slot = find_meeting_slot(common_free, meeting_duration, day, extra_min_start)
        if slot is not None:
            meeting_day = day
            meeting_time = slot
            break  # Choose the first available preferred slot

    if meeting_day and meeting_time:
        start_time_str = format_time(meeting_time[0])
        end_time_str = format_time(meeting_time[1])
        # Output the day and time range in the required format: HH:MM:HH:MM with the day.
        print(f"{meeting_day} {{{start_time_str}:{end_time_str}}}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()