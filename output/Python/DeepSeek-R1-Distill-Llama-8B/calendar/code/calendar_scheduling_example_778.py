import datetime

def find_meeting_time():
    # Define the meeting duration in minutes
    duration = 30  # 30 minutes

    # Convert start time to datetime.time object
    start_time = datetime.time(9)
    end_time = datetime.time(17)

    # Define each person's busy intervals
    susan_busy = [
        datetime.time(12, 30), datetime.time(13, 0),
        datetime.time(13, 30), datetime.time(14, 0)
    ]
    sandra_busy = [
        datetime.time(9, 0), datetime.time(10, 0),
        datetime.time(11, 0), datetime.time(12, 0),
        datetime.time(14, 0), datetime.time(14, 30),
        datetime.time(15, 0), datetime.time(15, 30),
        datetime.time(16, 0), datetime.time(16, 30),
        datetime.time(17, 0)
    ]

    # Convert busy intervals to time ranges
    def convert_intervals(intervals):
        all_time = set()
        for h, m in intervals:
            start = datetime.time(h, m)
            end = start + datetime.timedelta(minutes=1)
            all_time.add(start)
            all_time.add(end)
        return all_time

    susan_busy = convert_intervals(susan_busy)
    sandra_busy = convert_intervals(sandra_busy)

    # Check each minute from start_time to end_time - duration
    for minute in range(start_time.hour * 60, end_time.hour * 60 + 1):
        current = datetime.time(minute // 60, minute % 60)
        end = current + datetime.timedelta(minutes=duration)
        end_time = end.time()

        # Check if current minute is free for both
        if (current not in susan_busy and
            current not in sandra_busy):
            # Check if the entire duration fits in the day
            if end_time <= datetime.time(17, 0):
                return f"{current.hour:02d}:{current.minute:02d} to {end.hour:02d}:{end.minute:02d} on Monday"

    # If no slot found (shouldn't happen as per problem statement)
    return "No suitable time found"

# Get the result
result = find_meeting_time()
print(f"{result}")