def find_meeting_time():
    # Define the busy intervals for each participant in minutes since midnight
    # Format: (start_hour, start_minute, end_hour, end_minute)
    schedules = {
        "Natalie": [],
        "David": [(11, 30, 12, 0), (14, 30, 15, 0)],
        "Douglas": [(9, 30, 10, 0), (11, 30, 12, 0), (13, 0, 13, 30), (14, 30, 15, 0)],
        "Ralph": [(9, 0, 9, 30), (10, 0, 11, 0), (11, 30, 12, 30), (13, 30, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)],
        "Jordan": [(9, 0, 10, 0), (12, 0, 12, 30), (13, 0, 13, 30), (14, 30, 15, 0), (15, 30, 17, 0)]
    }

    day = "Monday"
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes in minutes

    # Combine all busy intervals
    all_busy = []
    for person in schedules:
        for interval in schedules[person]:
            start = interval[0] * 60 + interval[1]
            end = interval[2] * 60 + interval[3]
            all_busy.append((start, end))

    # Sort busy intervals by start time
    all_busy.sort(key=lambda x: x[0])

    # Check for available slots after 14:00 (David's constraint)
    current_time = max(start_time, 14 * 60)  # Start searching from 14:00

    for busy_start, busy_end in all_busy:
        if busy_start > current_time:
            # Check if there's a gap before the next busy interval
            if current_time + meeting_duration <= busy_start:
                meeting_start = current_time
                meeting_end = meeting_start + meeting_duration
                return f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d} on {day}"
        current_time = max(current_time, busy_end)

    # Check if there's time after the last busy interval
    if current_time + meeting_duration <= end_time:
        meeting_start = current_time
        meeting_end = meeting_start + meeting_duration
        return f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d} on {day}"

    return "No available time found"

print(find_meeting_time())