def main():
    # Convert time to minutes from 9:00 (base time)
    work_start_min = 0  # 9:00
    work_end_min = 480  # 17:00 (8 hours * 60 minutes)
    meeting_duration = 30

    # Initialize a list representing free times (True means free)
    free = [True] * work_end_min

    # Define busy intervals in minutes (relative to 9:00)
    emily_busy = [
        (60, 90),   # 10:00-10:30
        (150, 180), # 11:30-12:30
        (300, 360), # 14:00-15:00
        (420, 450)   # 16:00-16:30
    ]
    melissa_busy = [
        (30, 60),   # 9:30-10:00
        (330, 360)  # 14:30-15:00
    ]
    frank_busy = [
        (60, 90),   # 10:00-10:30
        (120, 150), # 11:00-11:30
        (210, 240), # 12:30-13:00
        (270, 330), # 13:30-14:30
        (360, 420), # 15:00-16:00
        (450, 480)  # 16:30-17:00
    ]

    # Mark busy times for Emily
    for start, end in emily_busy:
        for minute in range(start, min(end, work_end_min)):
            free[minute] = False

    # Mark busy times for Melissa
    for start, end in melissa_busy:
        for minute in range(start, min(end, work_end_min)):
            free[minute] = False

    # Mark busy times for Frank
    for start, end in frank_busy:
        for minute in range(start, min(end, work_end_min)):
            free[minute] = False

    # Frank's constraint: meeting must end by 9:30 (minute 30)
    # Check if [0, 30) is free for all
    slot_available = True
    for minute in range(0, meeting_duration):
        if not free[minute]:
            slot_available = False
            break

    if slot_available:
        start_minute = 0
        end_minute = meeting_duration
        # Convert minutes to HH:MM format
        start_hour = 9 + start_minute // 60
        start_min = start_minute % 60
        end_hour = 9 + end_minute // 60
        end_min = end_minute % 60
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print("Monday")
        print(time_str)
    else:
        # According to the problem, a solution exists, so this should not occur
        print("No valid time slot found")

if __name__ == "__main__":
    main()