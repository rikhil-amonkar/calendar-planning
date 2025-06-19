def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time_str(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    day = "Monday"
    duration = 30  # minutes
    work_start = 0  # 9:00 in minutes
    work_end = 480   # 17:00 in minutes

    # Initialize busy_count array for each minute in work hours (0 to 479 minutes)
    busy_count = [0] * (work_end)  # 0 to 479 minutes

    # Define busy intervals for each participant in minutes (start inclusive, end exclusive)
    participants_busy = {
        "Katherine": [
            ("12:00", "12:30"),
            ("13:00", "14:30")
        ],
        "Rebecca": [],
        "Julie": [
            ("9:00", "9:30"),
            ("10:30", "11:00"),
            ("13:30", "14:00"),
            ("15:00", "15:30")
        ],
        "Angela": [
            ("9:00", "10:00"),
            ("10:30", "11:00"),
            ("11:30", "14:00"),
            ("14:30", "15:00"),
            ("16:30", "17:00")
        ],
        "Nicholas": [
            ("9:30", "11:00"),
            ("11:30", "13:30"),
            ("14:00", "16:00"),
            ("16:30", "17:00")
        ],
        "Carl": [
            ("9:00", "11:00"),
            ("11:30", "12:30"),
            ("13:00", "14:30"),
            ("15:00", "16:00"),
            ("16:30", "17:00")
        ]
    }

    # Process each participant's busy intervals
    for person, intervals in participants_busy.items():
        for interval in intervals:
            start_str, end_str = interval
            start_min = time_str_to_minutes(start_str)
            end_min = time_str_to_minutes(end_str)
            for minute in range(start_min, end_min):
                if minute < work_end:
                    busy_count[minute] += 1

    # First, try to find a slot after 15:00 (360 minutes)
    start_minute_found = None
    for start in range(360, work_end - duration + 1):
        if all(busy_count[i] == 0 for i in range(start, start + duration)):
            start_minute_found = start
            break
    else:
        # If not found after 15:00, try the entire day (including before 15:00)
        for start in range(0, work_end - duration + 1):
            if all(busy_count[i] == 0 for i in range(start, start + duration)):
                start_minute_found = start
                break

    if start_minute_found is None:
        # According to the problem, there is a solution, so this should not happen.
        print("No suitable time found")
    else:
        start_time_str = minutes_to_time_str(start_minute_found)
        end_time_str = minutes_to_time_str(start_minute_found + duration)
        time_range_str = f"{start_time_str}:{end_time_str}"
        print(time_range_str)
        print(day)

if __name__ == "__main__":
    main()