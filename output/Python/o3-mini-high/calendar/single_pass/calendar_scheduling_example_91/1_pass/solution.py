def time_to_minutes(t):
    # Convert time string "HH:MM" to minutes since midnight.
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Convert minutes since midnight to time string "HH:MM".
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def is_free(interval_start, duration, busy_times):
    # Check if the time slot [interval_start, interval_start+duration) does not
    # conflict with any busy interval.
    interval_end = interval_start + duration
    for busy_start, busy_end in busy_times:
        # If the candidate interval overlaps with a busy interval, return False.
        if interval_start < busy_end and interval_end > busy_start:
            return False
    return True

def find_meeting_time(work_start, work_end, duration, schedules):
    # Starting from work_start, try every minute until there is room for a meeting.
    for start in range(work_start, work_end - duration + 1):
        if all(is_free(start, duration, busy) for busy in schedules):
            return start
    return None

def main():
    meeting_duration = 60  # meeting duration in minutes

    # Define workday start and end times on Monday.
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Busy intervals for each participant (times are in "HH:MM" format).
    danielle_busy = [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    bruce_busy = [
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
    
    eric_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30"))
    ]

    # List of busy intervals for all participants.
    schedules = [danielle_busy, bruce_busy, eric_busy]
    
    # Find the earliest meeting time that works for all.
    meeting_start = find_meeting_time(work_start, work_end, meeting_duration, schedules)
    
    # Output the result.
    if meeting_start is not None:
        meeting_end = meeting_start + meeting_duration
        print("Monday")
        print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()