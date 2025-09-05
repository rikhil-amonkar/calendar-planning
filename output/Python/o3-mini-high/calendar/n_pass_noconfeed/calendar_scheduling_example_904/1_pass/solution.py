def time_to_minutes(t):
    """Convert time string HH:MM to minutes from midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes from midnight to HH:MM format."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    """Given a list of busy intervals (in minutes), return a list of free intervals during work hours."""
    # Sort busy intervals by start time.
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """Find intersections between two lists of intervals."""
    intersections = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start_int = max(start1, start2)
            end_int = min(end1, end2)
            if start_int + 0 <= end_int:  # they overlap at least at a point
                intersections.append((start_int, end_int))
    return intersections

def adjust_for_preferences(day, free_intervals, person="Bradley"):
    """
    Adjust free intervals based on personal meeting preferences.
    For Bradley, he does not want to meet on Tuesday before 12:00 (720 minutes).
    (Other preferences are handled by filtering allowed days.)
    """
    adjusted = []
    if person == "Bradley" and day == "Tuesday":
        for start, end in free_intervals:
            new_start = max(start, 720)  # 12:00 = 720 minutes
            if new_start < end:
                adjusted.append((new_start, end))
        return adjusted
    return free_intervals

def main():
    meeting_duration = 30  # minutes
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes

    # Define busy schedules for each participant (times in HH:MM).
    schedule_daniel = {
        "Monday": [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "14:00"),
                   ("14:30", "15:00"), ("15:30", "16:00")],
        "Tuesday": [("11:00", "12:00"), ("13:00", "13:30"), ("15:30", "16:00"),
                    ("16:30", "17:00")],
        "Wednesday": [("09:00", "10:00"), ("14:00", "14:30")],
        "Thursday": [("10:30", "11:00"), ("12:00", "13:00"), ("14:30", "15:00"),
                     ("15:30", "16:00")],
        "Friday": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"),
                   ("16:30", "17:00")]
    }

    schedule_bradley = {
        "Monday": [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                   ("14:00", "15:00")],
        "Tuesday": [("10:30", "11:00"), ("12:00", "13:00"), ("13:30", "14:00"),
                    ("15:30", "16:30")],
        "Wednesday": [("09:00", "10:00"), ("11:00", "13:00"), ("13:30", "14:00"),
                      ("14:30", "17:00")],
        "Thursday": [("09:00", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"),
                     ("15:30", "16:30")],
        "Friday": [("09:00", "09:30"), ("10:00", "12:30"), ("13:00", "13:30"),
                   ("14:00", "14:30"), ("15:30", "16:30")]
    }

    # Convert all busy intervals from HH:MM strings to minutes.
    for person_schedule in (schedule_daniel, schedule_bradley):
        for day in person_schedule:
            person_schedule[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in person_schedule[day]]

    # Define allowed days based on meeting preferences.
    # Daniel would rather not meet on Wednesday and Thursday.
    allowed_daniel = {"Monday", "Tuesday", "Friday"}
    # Bradley does not want to meet on Monday and Friday, and on Tuesday he prefers meetings after 12:00.
    allowed_bradley = {"Tuesday", "Wednesday", "Thursday"}

    # Order of days in the work week.
    days_order = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    meeting_found = False
    proposed_day = None
    proposed_start = None
    proposed_end = None

    for day in days_order:
        # Check if both participants are willing to meet on this day.
        if day not in allowed_daniel or day not in allowed_bradley:
            continue

        # Compute free intervals for Daniel.
        busy_daniel = schedule_daniel.get(day, [])
        free_daniel = get_free_intervals(busy_daniel, work_start, work_end)

        # Compute free intervals for Bradley.
        busy_bradley = schedule_bradley.get(day, [])
        free_bradley = get_free_intervals(busy_bradley, work_start, work_end)
        free_bradley = adjust_for_preferences(day, free_bradley, person="Bradley")

        # Find intersections of free intervals.
        intersections = intersect_intervals(free_daniel, free_bradley)
        # Look for an intersection interval that can accommodate the meeting.
        for start, end in intersections:
            if end - start >= meeting_duration:
                proposed_day = day
                proposed_start = start
                proposed_end = start + meeting_duration
                meeting_found = True
                break
        if meeting_found:
            break

    if meeting_found:
        start_str = minutes_to_time(proposed_start)
        end_str = minutes_to_time(proposed_end)
        # Output in the format: Day and time range as HH:MM:HH:MM.
        print(f"{proposed_day} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()