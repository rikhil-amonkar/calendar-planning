def find_meeting_time():
    # Define the busy intervals for Olivia, Anna, Virginia, and Paul in minutes since midnight
    olivia_busy = [(12, 30, 13, 30), (14, 30, 15, 0), (16, 30, 17, 0)]
    anna_busy = []
    virginia_busy = [(9, 0, 10, 0), (11, 30, 16, 0), (16, 30, 17, 0)]
    paul_busy = [(9, 0, 9, 30), (11, 0, 11, 30), (13, 0, 14, 0), (14, 30, 16, 0), (16, 30, 17, 0)]

    day = "Monday"
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Combine all busy intervals
    all_busy = olivia_busy + anna_busy + virginia_busy + paul_busy
    all_busy.sort(key=lambda x: (x[0], x[1]))

    # Check for available slots
    current_time = start_time
    for busy_start, busy_end in all_busy:
        start = busy_start[0] * 60 + busy_start[1]
        end = busy_end[0] * 60 + busy_end[1]
        if current_time + meeting_duration <= start:
            # Found a slot
            meeting_start = current_time
            meeting_end = meeting_start + meeting_duration
            return f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d} on {day}"
        current_time = max(current_time, end)

    # Check if there's time after the last busy interval
    if current_time + meeting_duration <= end_time:
        meeting_start = current_time
        meeting_end = meeting_start + meeting_duration
        return f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d} on {day}"

    return "No available time found"

print(find_meeting_time())