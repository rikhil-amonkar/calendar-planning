def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def compute_free_intervals(busy, work_start, work_end):
    # Sort the busy intervals by start time
    busy = sorted(busy, key=lambda x: x[0])
    free = []
    current = work_start
    for b in busy:
        if current < b[0]:
            free.append((current, b[0]))
        current = max(current, b[1])
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    i = j = 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

# Define working hours (in minutes) 9:00 to 17:00
work_start = 9 * 60   # 540
work_end = 17 * 60    # 1020

# Meeting duration of 60 minutes.
meeting_duration = 60

# Define the schedules (busy intervals) for each participant in minutes.
# Each tuple is (start, end) in minutes from midnight.
schedules = {
    "Monday": {
        "Patricia": [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), 
                     (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), 
                     (16 * 60, 16 * 60 + 30)],
        "Jesse": [(9 * 60, 17 * 60)]
    },
    "Tuesday": {
        "Patricia": [(10 * 60, 10 * 60 + 30), (11 * 60, 12 * 60), 
                     (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
        "Jesse": [(11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), 
                  (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60), 
                  (15 * 60 + 30, 17 * 60)]
    }
}

# Attempt to find a meeting slot on either Monday or Tuesday.
proposed_day = None
proposed_start = None
proposed_end = None

for day in ["Monday", "Tuesday"]:
    # Get free intervals for each participant for the day.
    free_intervals = {}
    for person, busy in schedules[day].items():
        free_intervals[person] = compute_free_intervals(busy, work_start, work_end)
    
    # Compute the intersection of free intervals for Patricia and Jesse.
    common_free = intersect_intervals(free_intervals["Patricia"], free_intervals["Jesse"])
    
    # Now, check if any common free interval is at least meeting_duration minutes long.
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            proposed_day = day
            proposed_start = start
            proposed_end = start + meeting_duration
            break
    if proposed_day is not None:
        break

if proposed_day is not None:
    start_str = minutes_to_time(proposed_start)
    end_str = minutes_to_time(proposed_end)
    print(f"{start_str}:{end_str} {proposed_day}")
else:
    print("No available meeting slot found.")