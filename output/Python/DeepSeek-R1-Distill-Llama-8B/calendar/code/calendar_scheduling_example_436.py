import datetime

def find_meeting_time():
    # Define the meeting duration in minutes
    duration = 30  # 30 minutes

    # Convert start time to datetime.time object
    start_time = datetime.time(9)
    end_time = datetime.time(17)

    # Define each person's busy intervals
    patrick_busy = [
        (13, 30), (14, 0)
    ]
    shirley_busy = [
        (9, 0), (9, 30), (11, 0), (11, 30), (12, 0), (12, 30),
        (14, 30), (16, 0)
    ]
    jeffrey_busy = [
        (9, 0), (9, 30), (10, 30), (11, 0), (11, 30), (12, 0),
        (13, 0), (13, 30), (16, 0)
    ]
    gloria_busy = [
        (11, 30), (12, 0), (15, 0), (15, 30)
    ]
    nathan_busy = [
        (9, 0), (9, 30), (10, 30), (11, 0), (12, 0),
        (14, 0), (14, 30), (15, 0), (16, 0), (17, 0)
    ]
    angela_busy = [
        (9, 0), (9, 30), (10, 0), (11, 0), (12, 30), (13, 30),
        (14, 0), (15, 0), (15, 30), (16, 30), (17, 30)
    ]
    david_busy = [
        (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30),
        (12, 0), (12, 30), (13, 0), (13, 30), (14, 0),
        (16, 30), (17, 0), (17, 30)
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

    patrick_busy = convert_intervals(patrick_busy)
    shirley_busy = convert_intervals(shirley_busy)
    jeffrey_busy = convert_intervals(jeffrey_busy)
    gloria_busy = convert_intervals(gloria_busy)
    nathan_busy = convert_intervals(nathan_busy)
    angela_busy = convert_intervals(angela_busy)
    david_busy = convert_intervals(david_busy)

    # Check each minute from start_time to end_time - duration
    for minute in range(start_time.hour * 60, end_time.hour * 60 + 1):
        current = datetime.time(minute // 60, minute % 60)
        end = current + datetime.timedelta(minutes=duration)
        end_time = end.time()

        # Check if current minute is free for everyone
        if (current not in patrick_busy and
            current not in shirley_busy and
            current not in jeffrey_busy and
            current not in gloria_busy and
            current not in nathan_busy and
            current not in angela_busy and
            current not in david_busy):
            # Check if the entire duration fits in the day
            if end_time <= datetime.time(17, 0):
                return f"{current.hour:02d}:{current.minute:02d} to {end.hour:02d}:{end.minute:02d} on Monday"

    # If no slot found (shouldn't happen as per problem statement)
    return "No suitable time found"

# Get the result
result = find_meeting_time()
print(f"{result}")