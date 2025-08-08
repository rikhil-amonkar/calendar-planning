def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, window_start, window_end):
    free = []
    current = window_start
    # Sort busy intervals by their start time
    for interval in sorted(busy, key=lambda x: x[0]):
        start, end = interval
        # Only consider busy intervals that overlap with the working window.
        if end <= window_start or start >= window_end:
            continue
        # Clip the busy interval to the working window
        busy_start = max(start, window_start)
        busy_end = min(end, window_end)
        if busy_start > current:
            free.append((current, busy_start))
        current = max(current, busy_end)
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(intervals1, intervals2, duration):
    common = []
    for (s1, e1) in intervals1:
        for (s2, e2) in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start >= duration:
                common.append((start, end))
    return common

# Define working hours in minutes (9:00 -> 17:00)
WORK_START = 9 * 60      # 540
WORK_END = 17 * 60       # 1020
MEETING_DURATION = 60

# Busy schedules (times in minutes from midnight)
# Stephanie's schedule
schedules = {
    "Monday": {
        "Stephanie": [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (14*60, 14*60+30)],
        "Betty":     [(9*60, 10*60), (11*60, 11*60+30), (14*60+30, 15*60), (15*60+30, 16*60)]
    },
    "Tuesday": {
        "Stephanie": [(12*60, 13*60)],
        # Betty is busy on Tuesday: note that Betty cannot meet after 12:30,
        # so we will restrict her available window to 9:00–12:30.
        "Betty":     [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 14*60+30), (15*60+30, 16*60)]
    },
    "Wednesday": {
        "Stephanie": [(9*60, 10*60), (13*60, 14*60)],
        "Betty":     [(10*60, 11*60+30), (12*60, 14*60), (14*60+30, 17*60)]
    }
}

# Working windows for each day; note that on Tuesday Betty cannot meet after 12:30.
working_windows = {
    "Monday": (WORK_START, WORK_END),
    "Tuesday": {
        "Stephanie": (WORK_START, WORK_END),
        "Betty": (WORK_START, 12*60+30)  # 9:00 to 12:30
    },
    "Wednesday": (WORK_START, WORK_END)
}

# We want to avoid Monday if possible, so preferred days order: Tuesday, Wednesday, then Monday.
preferred_days = ["Tuesday", "Wednesday", "Monday"]

meeting_day = None
meeting_start = None

for day in preferred_days:
    free = {}
    for person in ["Stephanie", "Betty"]:
        if day == "Tuesday":
            # Use the restricted working window for Betty on Tuesday
            window = working_windows[day][person] if person == "Betty" else working_windows[day]["Stephanie"]
        else:
            window = working_windows[day]
        free[person] = get_free_intervals(schedules[day][person], window[0], window[1])
    
    # Find common free intervals for both participants that can accommodate the meeting
    common_free = intersect_intervals(free["Stephanie"], free["Betty"], MEETING_DURATION)
    if common_free:
        # Choose the earliest available slot
        meeting_day = day
        meeting_start = common_free[0][0]
        break

if meeting_day is not None:
    meeting_end = meeting_start + MEETING_DURATION
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output format: day with time range in HH:MM:HH:MM
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No meeting slot available.")