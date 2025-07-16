total_minutes = 480  # 9:00 to 17:00 is 8 hours = 480 minutes
busy_flags = [False] * total_minutes

# Define the participants' busy times as list of (start, end) time strings
participants = {
    "Bradley": [("9:30", "10:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00")],
    "Teresa": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00")],
    "Elizabeth": [("9:00", "9:30"), ("10:30", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Christian": [("9:00", "9:30"), ("10:30", "17:00")]
}

def time_to_minutes(time_str):
    """Convert a time string (HH:MM) to minutes since 9:00."""
    h, m = map(int, time_str.split(':'))
    return (h - 9) * 60 + m

# Mark the busy minutes for each participant
for person, intervals in participants.items():
    for interval in intervals:
        start_str, end_str = interval
        start_minute = time_to_minutes(start_str)
        end_minute = time_to_minutes(end_str)
        # If the interval starts after 17:00, skip
        if start_minute >= total_minutes:
            continue
        # Cap the end_minute at total_minutes
        if end_minute > total_minutes:
            end_minute = total_minutes
        # Mark the minutes from start_minute to end_minute (exclusive) as busy
        for minute in range(start_minute, end_minute):
            if minute < total_minutes:
                busy_flags[minute] = True

# Find the first 30-minute free slot
for start in range(0, total_minutes - 29):
    if not any(busy_flags[start:start+30]):
        abs_start_minutes = 9 * 60 + start
        h1 = abs_start_minutes // 60
        m1 = abs_start_minutes % 60
        abs_end_minutes = abs_start_minutes + 30
        h2 = abs_end_minutes // 60
        m2 = abs_end_minutes % 60
        print("Monday")
        print(f"{h1:02d}:{m1:02d}:{h2:02d}:{m2:02d}")
        break