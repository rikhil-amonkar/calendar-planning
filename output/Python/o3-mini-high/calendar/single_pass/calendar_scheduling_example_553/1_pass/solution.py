def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, blocked):
    free = []
    current = work_start
    for start, end in sorted(blocked, key=lambda x: x[0]):
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            intersections.append((start, end))
        # Move the pointer in the interval that finishes first
        if e1 < e2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    # Working hours: 9:00 to 17:00 (in minutes)
    work_start = 9 * 60       # 540 minutes
    work_end   = 17 * 60      # 1020 minutes
    meeting_duration = 30     # 30 minutes meeting

    # Set the day of the meeting.
    day = "Monday"

    # Eric's blocked intervals on Monday:
    eric_blocked = [
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ]

    # Henry's blocked intervals on Monday:
    henry_blocked = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]

    # Calculate free intervals for both Eric and Henry
    eric_free = get_free_intervals(work_start, work_end, eric_blocked)
    henry_free = get_free_intervals(work_start, work_end, henry_blocked)

    # Common free time available for both
    common_free = intersect_intervals(eric_free, henry_free)

    # Henry's preference: Do not meet after 10:00.
    # So we require that the meeting ends by 10:00, i.e., meeting_start + meeting_duration <= 10:00.
    latest_meeting_end = time_to_minutes("10:00")

    meeting_time = None
    for interval in common_free:
        start_interval, end_interval = interval
        # Ensure the meeting would end by the earlier of interval end or 10:00.
        valid_end = min(end_interval, latest_meeting_end)
        if start_interval + meeting_duration <= valid_end:
            meeting_time = (start_interval, start_interval + meeting_duration)
            break

    if meeting_time:
        start_str = minutes_to_time(meeting_time[0])
        end_str   = minutes_to_time(meeting_time[1])
        # Output in the format "Day HH:MM:HH:MM"
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()