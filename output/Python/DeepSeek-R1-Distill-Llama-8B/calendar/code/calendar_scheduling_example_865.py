import datetime

def find_meeting_time():
    # Define the meeting duration in minutes
    duration = 60  # 60 minutes

    # Convert start time to datetime.time object
    start_time = datetime.time(9)
    end_time = datetime.time(17)

    # Define each person's busy intervals
    megan_busy = [
        (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30),
        (9, 0), (9, 30), (12, 0), (12, 30), (16, 0), (16, 30),
        (9, 30), (10, 0), (10, 30), (11, 30), (12, 0), (12, 30),
        (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30),
        (16, 0), (16, 30), (17, 0), (17, 30)
    ]
    daniel_busy = [
        (10, 0), (10, 30), (11, 30), (12, 30), (13, 0), (13, 30),
        (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30),
        (17, 0), (17, 30),
        (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30),
        (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30),
        (15, 0), (15, 30), (16, 0), (16, 30), (17, 0), (17, 30),
        (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30),
        (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30),
        (15, 0), (15, 30), (16, 0), (16, 30), (17, 0), (17, 30),
        (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30),
        (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30),
        (15, 0), (15, 30), (16, 0), (16, 30), (17, 0), (17, 30),
        (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30),
        (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30),
        (15, 0), (15, 30), (16, 0), (16, 30), (17, 0), (17, 30)
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

    megan_busy = convert_intervals(megan_busy)
    daniel_busy = convert_intervals(daniel_busy)

    # Check each day from Monday to Thursday
    for day in [datetime.weekday(), datetime.weekday() + 1, datetime.weekday() + 2, datetime.weekday() + 3]:
        current_day = datetime.date.fromisoformat('2023-10-09') + datetime.timedelta(days=day)
        start_day = current_day.replace(hour=9, minute=0)
        end_day = current_day.replace(hour=17, minute=0)

        # Check each minute from start_time to end_time - duration
        for minute in range(start_day.hour * 60, end_day.hour * 60 + 1):
            current = datetime.time(minute // 60, minute % 60)
            end = current + datetime.timedelta(minutes=duration)
            end_time = end.time()

            # Check if current minute is free for both
            if (current not in megan_busy and
                current not in daniel_busy):
                # Check if the entire duration fits in the day
                if end_time <= datetime.time(17, 0):
                    return f"{current.hour:02d}:{current.minute:02d} to {end.hour:02d}:{end.minute:02d} on {current_day.weekday():02d} days"

    # If no slot found (shouldn't happen as per problem statement)
    return "No suitable time found"

# Get the result
result = find_meeting_time()
print(f"{result}")