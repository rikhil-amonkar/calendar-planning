def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def is_free(busy_intervals, meeting_start, meeting_end):
    # A meeting is conflict‐free if it does NOT overlap any busy interval.
    for start, end in busy_intervals:
        # If meeting_start is before busy end and meeting_end is after busy start, they overlap.
        if meeting_start < end and meeting_end > start:
            return False
    return True

def main():
    # Define work hours: 9:00 (9*60 = 540) to 17:00 (17*60 = 1020)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30  # in minutes

    # Busy intervals for each participant (in minutes since midnight)
    busy = {
        "Doris": [(9 * 60, 11 * 60), (13 * 60 + 30, 14 * 60), (16 * 60, 16 * 60 + 30)],
        "Theresa": [(10 * 60, 12 * 60)],
        "Christian": [],
        "Terry": [
            (9 * 60 + 30, 10 * 60),
            (11 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 14 * 60),
            (14 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 17 * 60)
        ],
        "Carolyn": [
            (9 * 60, 10 * 60 + 30),
            (11 * 60, 11 * 60 + 30),
            (12 * 60, 13 * 60),
            (13 * 60 + 30, 14 * 60 + 30),
            (15 * 60, 17 * 60)
        ],
        "Kyle": [
            (9 * 60, 9 * 60 + 30),
            (11 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (14 * 60 + 30, 17 * 60)
        ]
    }

    # Iterate through possible starting times (in minutes) during work hours.
    # The meeting must finish by work_end.
    meeting_time = None
    for candidate_start in range(work_start, work_end - meeting_duration + 1):
        candidate_end = candidate_start + meeting_duration
        available = True

        for person, busy_intervals in busy.items():
            if not is_free(busy_intervals, candidate_start, candidate_end):
                available = False
                break

        if available:
            meeting_time = (candidate_start, candidate_end)
            break

    # Convert the meeting's start and end times to HH:MM format and output.
    if meeting_time:
        start_time_str = minutes_to_str(meeting_time[0])
        end_time_str = minutes_to_str(meeting_time[1])
        # Output format: Day HH:MM:HH:MM (e.g., Monday 13:00:13:30)
        print("Monday", f"{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()