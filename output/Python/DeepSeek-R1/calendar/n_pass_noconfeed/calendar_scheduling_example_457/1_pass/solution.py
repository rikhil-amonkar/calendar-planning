def main():
    # Work hours: 9:00 to 17:00 (480 minutes from 0 to 479)
    total_minutes = 480
    meeting_duration = 30  # minutes

    # Convert time string to minutes past 9:00
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return (hours - 9) * 60 + minutes

    # Convert minutes back to time string
    def minutes_to_time_str(m):
        hours = 9 + m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    # Initialize busy_count array for each minute (0 to 479)
    busy_count = [0] * total_minutes

    # Define the busy intervals for each participant
    participants = [
        ("Andrea", [("9:30", "10:30"), ("13:30", "14:30")]),
        ("Ruth", [("12:30", "13:00"), ("15:00", "15:30")]),
        ("Steven", [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("15:00", "16:00")]),
        ("Grace", []),
        ("Kyle", [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]),
        ("Elijah", [("9:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")]),
        ("Lori", [("9:00", "9:30"), ("10:00", "11:30"), ("12:00", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")])
    ]

    # Process each participant's busy intervals
    for name, intervals in participants:
        for interval in intervals:
            start_str, end_str = interval
            start_minute = time_str_to_minutes(start_str)
            end_minute = time_str_to_minutes(end_str)
            # Ensure the interval is within [0, total_minutes)
            start_minute = max(0, start_minute)
            end_minute = min(end_minute, total_minutes)
            # Mark each minute in the interval as busy
            for minute in range(start_minute, end_minute):
                if minute < total_minutes:
                    busy_count[minute] += 1

    # Find the first 30-minute free slot
    found = False
    start_index = -1
    for start in range(0, total_minutes - meeting_duration + 1):
        # Check if the next 'meeting_duration' minutes are free for everyone
        if all(busy_count[i] == 0 for i in range(start, start + meeting_duration)):
            found = True
            start_index = start
            break

    if found:
        start_time_str = minutes_to_time_str(start_index)
        end_time_str = minutes_to_time_str(start_index + meeting_duration)
        time_range_str = f"{start_time_str}:{end_time_str}"
        print("Monday")
        print(time_range_str)
    else:
        # According to the problem, there is a solution, so this should not happen.
        print("No suitable time found.")

if __name__ == "__main__":
    main()