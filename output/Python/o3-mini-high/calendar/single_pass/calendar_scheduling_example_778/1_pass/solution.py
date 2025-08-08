def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    busy = sorted(busy, key=lambda x: x[0])
    free = []
    current = work_start
    for b in busy:
        if b[0] > current:
            free.append((current, b[0]))
        current = max(current, b[1])
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(int1, int2):
    start = max(int1[0], int2[0])
    end = min(int1[1], int2[1])
    if start < end:
        return (start, end)
    return None

# Working hours and meeting duration in minutes
WORK_START = 9 * 60      # 9:00 -> 540
WORK_END = 17 * 60       # 17:00 -> 1020
MEETING_DURATION = 30    # 30 minutes

# Busy schedules given in minutes (start, end)
schedules = {
    "Monday": {
        "Susan": [(12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60)],      # 12:30-13:00, 13:30-14:00
        "Sandra": [(9 * 60, 13 * 60), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)]  # 9:00-13:00, 14:00-15:00, 16:00-16:30
    },
    "Tuesday": {
        "Susan": [(11 * 60 + 30, 12 * 60)],                                 # 11:30-12:00
        "Sandra": [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), 
                   (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 14 * 60 + 30),
                   (16 * 60, 17 * 60)]                                   # 9:00-9:30, 10:30-12:00, 12:30-13:30, 14:00-14:30, 16:00-17:00
    },
    "Wednesday": {
        "Susan": [(9 * 60 + 30, 10 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)],  # 9:30-10:30, 14:00-14:30, 15:30-16:30
        "Sandra": [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)]  # 9:00-11:30, 12:00-12:30, 13:00-17:00
    }
}

# Preference: Susan would rather not meet on Tuesday so we try Monday and Wednesday first.
preferred_days = ["Monday", "Wednesday", "Tuesday"]

meeting_day = None
meeting_start = None
meeting_end = None

for day in preferred_days:
    # Compute each participant's free intervals within working hours.
    susan_free = get_free_intervals(schedules[day]["Susan"], WORK_START, WORK_END)
    sandra_free = get_free_intervals(schedules[day]["Sandra"], WORK_START, WORK_END)
    
    candidate_found = False
    # Try each pair of free intervals to find an overlapping slot.
    for interval_s in susan_free:
        for interval_sa in sandra_free:
            intersection = intersect_intervals(interval_s, interval_sa)
            if not intersection:
                continue
            start_int, end_int = intersection
            # For Monday, Sandra cannot meet after 16:00.
            if day == "Monday":
                end_int = min(end_int, 16 * 60)  # 16:00 -> 960 minutes
            if end_int - start_int >= MEETING_DURATION:
                # Schedule meeting to start at the beginning of the available window.
                meeting_day = day
                meeting_start = start_int
                meeting_end = start_int + MEETING_DURATION
                candidate_found = True
                break
        if candidate_found:
            break
    if candidate_found:
        break

if meeting_day:
    # Output in the format "Day HH:MM:HH:MM"
    print(f"{meeting_day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
else:
    print("No available time slot found.")