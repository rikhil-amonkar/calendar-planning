def parse_time(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    free = []
    current = work_start
    for start, end in sorted(busy_intervals, key=lambda x: x[0]):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals."""
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        start = max(list1[i][0], list2[j][0])
        end = min(list1[i][1], list2[j][1])
        if start < end:
            result.append((start, end))
        if list1[i][1] < list2[j][1]:
            i += 1
        else:
            j += 1
    return result

# Meeting duration in minutes (1 hour)
meeting_duration = 60

# Work hours (9:00 to 17:00)
work_start = parse_time("09:00")
work_end = parse_time("17:00")

# Define participants' busy schedules for each day in HH:MM format.
schedules = {
    "Monday": {
        "Patricia": [
            (parse_time("10:00"), parse_time("10:30")),
            (parse_time("11:30"), parse_time("12:00")),
            (parse_time("13:00"), parse_time("13:30")),
            (parse_time("14:30"), parse_time("15:30")),
            (parse_time("16:00"), parse_time("16:30"))
        ],
        "Jesse": [
            (parse_time("09:00"), parse_time("17:00"))
        ]
    },
    "Tuesday": {
        "Patricia": [
            (parse_time("10:00"), parse_time("10:30")),
            (parse_time("11:00"), parse_time("12:00")),
            (parse_time("14:00"), parse_time("16:00")),
            (parse_time("16:30"), parse_time("17:00"))
        ],
        "Jesse": [
            (parse_time("11:00"), parse_time("11:30")),
            (parse_time("12:00"), parse_time("12:30")),
            (parse_time("13:00"), parse_time("14:00")),
            (parse_time("14:30"), parse_time("15:00")),
            (parse_time("15:30"), parse_time("17:00"))
        ]
    }
}

# Try to find a common 60-minute slot on either Monday or Tuesday.
found = False
for day in ["Monday", "Tuesday"]:
    # Compute free intervals for each participant.
    free_intervals = {}
    for person, busy in schedules[day].items():
        free_intervals[person] = get_free_intervals(work_start, work_end, busy)
    
    # Get common free intervals between the two participants.
    common_free = intersect_intervals(free_intervals["Patricia"], free_intervals["Jesse"])
    
    # Check if any common interval can accommodate the meeting duration.
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            # Output format: Day followed by HH:MM:HH:MM time range.
            print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            found = True
            break
    if found:
        break

if not found:
    print("No available meeting time found within the constraints.")