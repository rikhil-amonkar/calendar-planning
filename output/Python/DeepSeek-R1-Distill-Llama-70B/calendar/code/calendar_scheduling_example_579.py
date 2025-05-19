def find_meeting_time():
    # Define the busy intervals for Christine and Helen in minutes since midnight
    christine_busy = [(11 * 60 + 0, 11 * 60 + 30),  # 11:00 to 11:30
                      (15 * 60 + 0, 15 * 60 + 30)]  # 15:00 to 15:30

    helen_busy = [(9 * 60 + 30, 10 * 60 + 30),  # 9:30 to 10:30
                  (11 * 60 + 0, 11 * 60 + 30),  # 11:00 to 11:30
                  (12 * 60 + 0, 12 * 60 + 30),  # 12:00 to 12:30
                  (13 * 60 + 30, 16 * 60 + 0),  # 13:30 to 16:00
                  (16 * 60 + 30, 17 * 60 + 0)]  # 16:30 to 17:00

    day = "Monday"
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes in minutes

    # Combine and sort all busy intervals
    all_busy = christine_busy + helen_busy
    all_busy.sort(key=lambda x: x[0])

    # Check for available slots
    current_time = start_time
    for busy_start, busy_end in all_busy:
        if current_time + meeting_duration <= busy_start:
            # Found a slot
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