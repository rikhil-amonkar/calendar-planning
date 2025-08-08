def time_to_minutes(t):
    """Convert a time string HH:MM into minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight into a time string HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (tuples of (start, end) in minutes),
    return a list of free time intervals within the work window.
    """
    # Sort busy intervals by their start time.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def get_earliest_slot(robert_busy, ralph_busy, meeting_duration, work_start, work_end):
    """
    Compute the earliest possible meeting slot (of duration meeting_duration in minutes)
    from the intersection of Robert's and Ralph's free intervals.
    """
    robert_free = get_free_intervals(robert_busy, work_start, work_end)
    ralph_free = get_free_intervals(ralph_busy, work_start, work_end)
    
    earliest_slot = None
    # Check intersections of free intervals for both persons.
    for r_start, r_end in robert_free:
        for a_start, a_end in ralph_free:
            start = max(r_start, a_start)
            end = min(r_end, a_end)
            # If the intersected interval is long enough, take its earliest possible slot.
            if end - start >= meeting_duration:
                if earliest_slot is None or start < earliest_slot[0]:
                    earliest_slot = (start, start + meeting_duration)
    return earliest_slot

def main():
    work_start_str = "09:00"
    work_end_str   = "17:00"
    work_start = time_to_minutes(work_start_str)
    work_end = time_to_minutes(work_end_str)
    meeting_duration = 30  # in minutes

    # Define busy schedules for each participant on each day.
    schedules = {
        "Monday": {
            "Robert": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
            "Ralph":  [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")]
        },
        "Tuesday": {
            "Robert": [("10:30", "11:00"), ("15:00", "15:30")],
            "Ralph":  [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"),
                       ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")]
        },
        "Wednesday": {
            "Robert": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                       ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
            "Ralph":  [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"),
                       ("16:30", "17:00")]
        }
    }

    # Convert all time strings in schedules to minutes.
    for day in schedules:
        for person in schedules[day]:
            schedules[day][person] = [
                (time_to_minutes(start), time_to_minutes(end))
                for start, end in schedules[day][person]
            ]

    # Because Robert wants to avoid more meetings on Monday,
    # we prefer Tuesday, then Wednesday, then Monday.
    preferred_days = ["Tuesday", "Wednesday", "Monday"]
    meeting_day = None
    meeting_slot = None

    for day in preferred_days:
        robert_busy = schedules[day]["Robert"]
        ralph_busy  = schedules[day]["Ralph"]
        slot = get_earliest_slot(robert_busy, ralph_busy, meeting_duration, work_start, work_end)
        if slot is not None:
            meeting_day = day
            meeting_slot = slot
            break

    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        # Output the result in the format: Day {HH:MM:HH:MM}
        # For example: Tuesday {09:30:10:00}
        print(f"{meeting_day} {{{start_time}:{end_time}}}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()