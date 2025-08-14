def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy intervals for each participant in minutes since midnight
busy_ashley = [
    (600, 630),  # 10:00-10:30
    (660, 720),  # 11:00-12:00
    (750, 780),  # 12:30-13:00
    (900, 960),  # 15:00-16:00
]

busy_ronald = [
    (540, 570),   # 9:00-9:30
    (600, 690),   # 10:00-11:30
    (750, 840),   # 12:30-14:00
    (870, 1020),  # 14:30-17:00
]

busy_larry = [
    (540, 720),   # 9:00-12:00
    (780, 1020),  # 13:00-17:00
]

busy_erich = []

# List of all participants' busy intervals
busy_list_list = [busy_erich, busy_ashley, busy_ronald, busy_larry]

# Workday start and end in minutes
work_start = 540  # 9:00
work_end = 1020   # 17:00
meeting_duration = 30

# Find the earliest possible slot
found = False
for start in range(work_start, work_end - meeting_duration + 1):
    end = start + meeting_duration
    # Check if this slot is free for all
    valid = True
    for busy_list in busy_list_list:
        for (s, e) in busy_list:
            # Check overlap between [start, end) and [s, e)
            if not (end <= s or start >= e):
                valid = False
                break
        if not valid:
            break
    if valid:
        # Convert to time strings
        start_time = to_time_str(start)
        end_time = to_time_str(end)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        found = True
        break

if not found:
    print("No suitable time found.")