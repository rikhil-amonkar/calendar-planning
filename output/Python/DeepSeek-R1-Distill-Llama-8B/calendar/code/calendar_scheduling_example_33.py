import datetime

def find_meeting_time():
    # Define the meeting duration in minutes
    duration = 30  # 30 minutes

    # Convert start time to datetime.time object
    start_time = datetime.time(9)
    end_time = datetime.time(17)

    # Define each person's busy intervals
    lisa_busy = [
        (9, 0), (10, 30), (12, 30), (16, 0)
    ]
    bobby_busy = [
        (9, 0), (10, 30), (11, 30), (15, 0)
    ]
    randy_busy = [
        (9, 30), (10, 30), (11, 30), (13, 0), (14, 30), (16, 0)
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

    lisa_busy = convert_intervals(lisa_busy)
    bobby_busy = convert_intervals(bobby_busy)
    randy_busy = convert_intervals(randy_busy)

    # Check each minute from start_time to end_time - duration
    for minute in range(start_time.hour * 60, end_time.hour * 60 + 1):
        current = datetime.time(minute // 60, minute % 60)
        end = current + datetime.timedelta(minutes=duration)
        end_time = end.time()

        # Check if current minute is free for everyone
        if (current not in lisa_busy and
            current not in bobby_busy and
            current not in randy_busy):
            # Check if the entire duration fits in the day
            if end_time <= datetime.time(17, 0):
                return f"{current.hour:02d}:{current.minute:02d} to {end.hour:02d}:{end.minute:02d} on Monday"

    # If no slot found (shouldn't happen as per problem statement)
    return "No suitable time found"

# Get the result
result = find_meeting_time()
print(f"{result}")