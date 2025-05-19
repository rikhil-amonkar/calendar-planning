def to_minutes(time_str):
    # Convert "HH:MM" to minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_time_str(minutes):
    # Convert minutes since midnight back to "HH:MM"
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_slots(busy_slots, work_start, work_end):
    # busy_slots is a list of tuples (start, end) in minutes, assumed sorted and non-overlapping.
    free = []
    current = work_start
    for start, end in busy_slots:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Given two lists of intervals, returns list of intersections
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int < end_int:
            intersection.append((start_int, end_int))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Define working hours in minutes (9:00 to 17:00)
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 60  # meeting length in minutes

# Busy schedules in minutes for each participant on each day.
# Format: day: list of (start, end) times in minutes.
natalie_busy = {
    "Monday": [(to_minutes("09:00"), to_minutes("09:30")),
               (to_minutes("10:00"), to_minutes("12:00")),
               (to_minutes("12:30"), to_minutes("13:00")),
               (to_minutes("14:00"), to_minutes("14:30")),
               (to_minutes("15:00"), to_minutes("16:30"))],
    "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("10:30")),
                (to_minutes("12:30"), to_minutes("14:00")),
                (to_minutes("16:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
    "Thursday": [(to_minutes("10:00"), to_minutes("11:00")),
                 (to_minutes("11:30"), to_minutes("15:00")),
                 (to_minutes("15:30"), to_minutes("16:00")),
                 (to_minutes("16:30"), to_minutes("17:00"))]
}

william_busy = {
    "Monday": [(to_minutes("09:30"), to_minutes("11:00")),
               (to_minutes("11:30"), to_minutes("17:00"))],
    "Tuesday": [(to_minutes("09:00"), to_minutes("13:00")),
                (to_minutes("13:30"), to_minutes("16:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("14:30")),
                  (to_minutes("15:30"), to_minutes("16:00")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
    "Thursday": [(to_minutes("09:00"), to_minutes("10:30")),
                 (to_minutes("11:00"), to_minutes("11:30")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("13:00"), to_minutes("14:00")),
                 (to_minutes("15:00"), to_minutes("17:00"))]
}

# Ensure each busy list is sorted (they should be already by the given schedule)
for day in natalie_busy:
    natalie_busy[day].sort()
for day in william_busy:
    william_busy[day].sort()

# Try to find a valid meeting slot day by day.
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    natalie_free = get_free_slots(natalie_busy.get(day, []), work_start, work_end)
    william_free = get_free_slots(william_busy.get(day, []), work_start, work_end)
    
    common_free = intersect_intervals(natalie_free, william_free)
    
    # Look for an interval with at least the meeting duration
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            print(f"{day} {to_time_str(meeting_start)}:{to_time_str(meeting_end)}")
            exit(0)

print("No meeting slot available.")