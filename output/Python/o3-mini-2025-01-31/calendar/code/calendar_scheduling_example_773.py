from datetime import datetime, timedelta

# Meeting duration in minutes
meeting_duration = 60

# Work hours boundaries (in minutes from midnight)
work_start = 9 * 60   # 9:00 AM = 540 minutes
work_end = 17 * 60    # 5:00 PM = 1020 minutes

# Busy intervals for Roy, in minutes from midnight.
# Each interval is a tuple (start, end). We assume intervals in sorted order.
schedules = {
    "Monday": [
        (10 * 60, 11 * 60 + 30),   # 10:00 - 11:30
        (12 * 60, 13 * 60),        # 12:00 - 13:00
        (14 * 60, 14 * 60 + 30),   # 14:00 - 14:30
        (15 * 60, 17 * 60)         # 15:00 - 17:00
    ],
    "Tuesday": [
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 - 11:30
        (12 * 60, 14 * 60 + 30),         # 12:00 - 14:30
        (15 * 60, 15 * 60 + 30),         # 15:00 - 15:30
        (16 * 60, 17 * 60)               # 16:00 - 17:00
    ],
    "Wednesday": [
        (9 * 60 + 30, 11 * 60 + 30),   # 9:30 - 11:30
        (12 * 60 + 30, 14 * 60),       # 12:30 - 14:00
        (14 * 60 + 30, 15 * 60 + 30),  # 14:30 - 15:30
        (16 * 60 + 30, 17 * 60)        # 16:30 - 17:00
    ]
}

# Since Patrick is available all week, we only need to check Roy's schedule.
work_days = ["Monday", "Tuesday", "Wednesday"]

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_time():
    for day in work_days:
        busy_intervals = schedules.get(day, [])
        # sort busy intervals
        busy_intervals.sort()
        
        # Start at the beginning of the day
        current_time = work_start
        
        # Check gap before each busy interval
        for interval in busy_intervals:
            interval_start, interval_end = interval
            if interval_start - current_time >= meeting_duration:
                # Found a gap where meeting can be scheduled
                meeting_start = current_time
                meeting_end = meeting_start + meeting_duration
                return day, meeting_start, meeting_end
            # Move current time to after this busy interval if needed
            if current_time < interval_end:
                current_time = interval_end

        # Check gap after the last busy interval until end of work day.
        if work_end - current_time >= meeting_duration:
            meeting_start = current_time
            meeting_end = meeting_start + meeting_duration
            return day, meeting_start, meeting_end

    return None, None, None

day, meeting_start, meeting_end = find_meeting_time()

if day is not None:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Format output: HH:MM:HH:MM and day of week
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available meeting time found within the constraints.")