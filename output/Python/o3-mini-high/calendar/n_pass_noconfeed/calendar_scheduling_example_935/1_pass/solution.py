def time_to_minutes(t):
    # Convert time string "HH:MM" to total minutes
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Convert minutes back to time string "HH:MM"
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Given a list of busy intervals (in minutes), return free intervals within work hours.
    free = []
    current = work_start
    # Ensure busy intervals are sorted by their start time.
    for start, end in sorted(busy_intervals, key=lambda x: x[0]):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Return intersections of two lists of intervals
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Determine overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersections.append((start_overlap, end_overlap))
        # Advance the interval that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # meeting duration in minutes

    # Busy schedules for Terry and Frances given as (start, end) in string format.
    terry_schedule = {
        "Monday": [("10:30", "11:00"), ("12:30", "14:00"), ("15:00", "17:00")],
        "Tuesday": [("09:30", "10:00"), ("10:30", "11:00"), ("14:00", "14:30"), ("16:00", "16:30")],
        "Wednesday": [("09:30", "10:30"), ("11:00", "12:00"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Thursday": [("09:30", "10:00"), ("12:00", "12:30"), ("13:00", "14:30"), ("16:00", "16:30")],
        "Friday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")]
    }

    frances_schedule = {
        "Monday": [("09:30", "11:00"), ("11:30", "13:00"), ("14:00", "14:30"), ("15:00", "16:00")],
        "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("13:00", "14:30"), ("15:30", "16:30")],
        "Wednesday": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")],
        "Thursday": [("11:00", "12:30"), ("14:30", "17:00")],
        "Friday": [("09:30", "10:30"), ("11:00", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")]
    }

    # Convert all busy times to minutes.
    for day in terry_schedule:
        terry_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) 
                               for start, end in terry_schedule[day]]
    for day in frances_schedule:
        frances_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) 
                                 for start, end in frances_schedule[day]]

    # Preferred order: Avoid Tuesday if possible.
    preferred_days = ["Monday", "Wednesday", "Thursday", "Friday", "Tuesday"]

    meeting_day = None
    meeting_start = None

    for day in preferred_days:
        # Skip days if either person doesn't have a schedule entry.
        if day not in terry_schedule or day not in frances_schedule:
            continue

        terry_free = get_free_intervals(terry_schedule[day], work_start, work_end)
        frances_free = get_free_intervals(frances_schedule[day], work_start, work_end)
        common_free = intersect_intervals(terry_free, frances_free)

        # Look for the earliest common free interval that can fit the meeting duration.
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_day = day
                meeting_start = start
                break
        if meeting_day is not None:
            break

    if meeting_day is not None:
        meeting_end = meeting_start + meeting_duration
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        # Output format: Day HH:MM:HH:MM
        print(f"{meeting_day} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()