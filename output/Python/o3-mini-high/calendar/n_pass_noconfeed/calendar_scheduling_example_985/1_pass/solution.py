def time_to_minutes(t):
    # Convert a time string "HH:MM" into minutes since midnight.
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Convert minutes since midnight into a time string "HH:MM".
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    # Given a list of busy intervals and work hours, return free intervals.
    free = []
    current = work_start
    # Sort busy intervals by their start time.
    for interval in sorted(busy, key=lambda x: x[0]):
        b_start, b_end = interval
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Compute intersections between two lists of intervals.
    intersections = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start > 0:
                intersections.append((start, end))
    return intersections

def find_meeting_slot(days, diane_busy, matthew_busy, meeting_duration, work_start, work_end):
    for day in days:
        # Compute free intervals for each participant.
        diane_free = get_free_intervals(diane_busy.get(day, []), work_start, work_end)
        matthew_free = get_free_intervals(matthew_busy.get(day, []), work_start, work_end)
        # Find common free intervals.
        common_free = intersect_intervals(diane_free, matthew_free)
        for start, end in common_free:
            meeting_start = start
            # On Wednesday, Matthew prefers not to meet before 12:30 (750 minutes).
            if day == "Wednesday" and meeting_start < 750:
                meeting_start = 750
            if meeting_start + meeting_duration <= end:
                return day, meeting_start, meeting_start + meeting_duration
    return None, None, None

def main():
    # Define work hours: 9:00 to 17:00 in minutes.
    work_start = 9 * 60      # 540 minutes (9:00)
    work_end = 17 * 60       # 1020 minutes (17:00)
    meeting_duration = 60    # Meeting duration is 60 minutes

    # Busy schedules for Diane (in minutes)
    diane_busy = {
        "Monday": [(12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
        "Tuesday": [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (16 * 60, 17 * 60)],
        "Wednesday": [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
        "Thursday": [(15 * 60 + 30, 16 * 60 + 30)],
        "Friday": [(9 * 60 + 30, 11 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
    }

    # Busy schedules for Matthew (in minutes)
    matthew_busy = {
        "Monday": [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
        "Tuesday": [(9 * 60, 17 * 60)],
        "Wednesday": [(9 * 60, 11 * 60), (12 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
        "Thursday": [(9 * 60, 16 * 60)],
        "Friday": [(9 * 60, 17 * 60)]
    }

    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    day, meeting_start, meeting_end = find_meeting_slot(
        days, diane_busy, matthew_busy, meeting_duration, work_start, work_end
    )

    if day:
        # Output in the specified format: Day HH:MM:HH:MM
        print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()