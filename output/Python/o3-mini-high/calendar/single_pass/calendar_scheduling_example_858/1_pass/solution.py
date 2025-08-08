def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Return a list of free intervals (start, end) in minutes given busy intervals."""
    # Ensure busy intervals are sorted.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(interval1, interval2):
    start = max(interval1[0], interval2[0])
    end = min(interval1[1], interval2[1])
    if start < end:
        return (start, end)
    return None

def find_slot(free1, free2, duration):
    i, j = 0, 0
    while i < len(free1) and j < len(free2):
        intersection = intersect_intervals(free1[i], free2[j])
        if intersection:
            start, end = intersection
            if end - start >= duration:
                return start, start + duration
        # Move the pointer with the earlier finishing interval.
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return None

def schedule_meeting(duration):
    # Work hours: 09:00 (540 min) to 17:00 (1020 min)
    work_start = 540
    work_end = 1020

    # Busy schedules in minutes for Carl and Margaret.
    carl_busy = {
        "Monday": [(time_to_minutes("11:00"), time_to_minutes("11:30"))],
        "Tuesday": [(time_to_minutes("14:30"), time_to_minutes("15:00"))],
        "Wednesday": [
            (time_to_minutes("10:00"), time_to_minutes("11:30")),
            (time_to_minutes("13:00"), time_to_minutes("13:30"))
        ],
        "Thursday": [
            (time_to_minutes("13:30"), time_to_minutes("14:00")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
    margaret_busy = {
        "Monday": [
            (time_to_minutes("09:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("17:00"))
        ],
        "Tuesday": [
            (time_to_minutes("09:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:30"), time_to_minutes("14:00")),
            (time_to_minutes("15:30"), time_to_minutes("17:00"))
        ],
        "Wednesday": [
            (time_to_minutes("09:30"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("13:00")),
            (time_to_minutes("13:30"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("17:00"))
        ],
        "Thursday": [
            (time_to_minutes("10:00"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("17:00"))
        ]
    }

    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    # Carl prefers to avoid Thursday meetings if possible.
    non_thursday = [day for day in days if day != "Thursday"]

    # First, try non-Thursday days.
    for day in non_thursday:
        carl_free = get_free_intervals(carl_busy.get(day, []), work_start, work_end)
        margaret_free = get_free_intervals(margaret_busy.get(day, []), work_start, work_end)
        slot = find_slot(carl_free, margaret_free, duration)
        if slot:
            return day, slot

    # Fallback to Thursday if no slot found on other days.
    day = "Thursday"
    carl_free = get_free_intervals(carl_busy.get(day, []), work_start, work_end)
    margaret_free = get_free_intervals(margaret_busy.get(day, []), work_start, work_end)
    slot = find_slot(carl_free, margaret_free, duration)
    if slot:
        return day, slot

    return None, None

def main():
    meeting_duration = 60  # minutes
    day, slot = schedule_meeting(meeting_duration)
    if slot:
        start, end = slot
        # Output in the format: Day HH:MM:HH:MM
        print(f"{day} {minutes_to_time(start)}:{minutes_to_time(end)}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()