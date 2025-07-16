def format_time(minutes):
    total_minutes = 9 * 60 + minutes
    hours = total_minutes // 60
    minutes_part = total_minutes % 60
    return f"{hours:02d}:{minutes_part:02d}"

# Define the busy intervals for each participant (in minutes relative to 9:00, as [start, end))
busy_intervals_jacqueline = [
    (0, 30),    # 9:00-9:30
    (120, 150), # 11:00-11:30
    (210, 240), # 12:30-13:00
]

busy_intervals_harold = [
    (60, 90),   # 10:00-10:30
]

busy_intervals_arthur = [
    (0, 30),    # 9:00-9:30
    (60, 210),  # 10:00-12:30
]

busy_intervals_kelly = [
    (0, 30),    # 9:00-9:30
    (60, 120),  # 10:00-11:00
    (150, 210), # 11:30-12:30
]

# Combine all participants' busy intervals
all_busy = [
    busy_intervals_jacqueline,
    busy_intervals_harold,
    busy_intervals_arthur,
    busy_intervals_kelly
]

meeting_duration = 30
work_start = 0
constraint_end = 240  # 13:00 relative to 9:00 (4 hours in minutes)

# Candidate start times every 30 minutes from work_start to constraint_end - meeting_duration
candidate_starts = list(range(work_start, constraint_end - meeting_duration + 1, 30))

# Check each candidate start time
for start in candidate_starts:
    end = start + meeting_duration
    found = True
    for participant in all_busy:
        for interval in participant:
            # Check for overlap: [start, end) overlaps [interval_start, interval_end)
            if start < interval[1] and interval[0] < end:
                found = False
                break
        if not found:
            break
    if found:
        start_str = format_time(start)
        end_str = format_time(end)
        print("Monday")
        print(f"{start_str}:{end_str}")
        break