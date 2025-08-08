def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    # Sort busy intervals by start time
    busy = sorted(busy, key=lambda x: x[0])
    free = []
    last_end = work_start
    for start, end in busy:
        if start > last_end:
            free.append((last_end, start))
        last_end = max(last_end, end)
    if last_end < work_end:
        free.append((last_end, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap between intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersections.append((start_overlap, end_overlap))
        # Move to the next interval in the list that finishes first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Define work hours in minutes (9:00 to 17:00)
work_start = 9 * 60  # 540
work_end = 17 * 60   # 1020
meeting_duration = 30

# Busy schedules for Eugene (times in minutes from midnight)
busy_eugene = {
    "Monday": [(11*60, 12*60), (13*60+30, 14*60), (14*60+30, 15*60), (16*60, 16*60+30)],
    "Tuesday": [],
    "Wednesday": [(9*60, 9*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 15*60)],
    "Thursday": [(9*60+30, 10*60), (11*60, 12*60+30)],
    "Friday": [(10*60+30, 11*60), (12*60, 12*60+30), (13*60, 13*60+30)]
}

# Busy schedules for Eric
busy_eric = {
    "Monday": [(9*60, 17*60)],
    "Tuesday": [(9*60, 17*60)],
    "Wednesday": [(9*60, 11*60+30), (12*60, 14*60), (14*60+30, 16*60+30)],
    "Thursday": [(9*60, 17*60)],
    "Friday": [(9*60, 11*60), (11*60+30, 17*60)]
}

# Order of days to check (avoiding Wednesday if possible)
days_order = ["Monday", "Tuesday", "Thursday", "Friday", "Wednesday"]

meeting_day = None
meeting_start_time = None
meeting_end_time = None

for day in days_order:
    # Determine free intervals for each participant on this day
    free_eugene = get_free_intervals(busy_eugene.get(day, []), work_start, work_end)
    free_eric = get_free_intervals(busy_eric.get(day, []), work_start, work_end)
    
    # Find common free intervals
    common_free = intersect_intervals(free_eugene, free_eric)
    
    # Check if any free interval fits the meeting duration.
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_day = day
            meeting_start_time = start
            meeting_end_time = start + meeting_duration
            break
    if meeting_day is not None:
        break

if meeting_day is not None:
    start_str = minutes_to_str(meeting_start_time)
    end_str = minutes_to_str(meeting_end_time)
    # Output in the format HH:MM:HH:MM along with the day of the week.
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No available time slot found.")