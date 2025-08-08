def minutes_to_time(m):
    """Convert minutes since midnight into HH:MM string format."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start=540, work_end=1020):
    """
    Given a sorted list of busy intervals (start, end) in minutes,
    return a list of free intervals within work hours [work_start, work_end].
    """
    free = []
    current = work_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_intersection(free1, free2, meeting_dur):
    """
    Given two lists of free intervals (each interval as a tuple (start, end) in minutes)
    and a required meeting duration in minutes, find the earliest time interval (start, start+duration)
    that is common to both.
    """
    i, j = 0, 0
    while i < len(free1) and j < len(free2):
        # Calculate intersection of free1[i] and free2[j]
        start = max(free1[i][0], free2[j][0])
        end = min(free1[i][1], free2[j][1])
        if end - start >= meeting_dur:
            return start, start + meeting_dur
        # Advance in the list that ends earlier.
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return None  # no intersection long enough

# Define each participant's busy schedule in minutes (from 9:00=540 to 17:00=1020)
nicole_schedule = {
    "Monday": [],
    "Tuesday": [(16 * 60, 16 * 60 + 30)],         # 16:00 - 16:30 -> (960, 990)
    "Wednesday": [(15 * 60, 15 * 60 + 30)],         # 15:00 - 15:30 -> (900, 930)
    "Thursday": [],
    "Friday": [(12 * 60, 12 * 60 + 30),              # 12:00 - 12:30 -> (720, 750)
               (15 * 60 + 30, 16 * 60)]            # 15:30 - 16:00 -> (930, 960)
}

daniel_schedule = {
    "Monday": [
        (9 * 60, 12 * 60 + 30),                     # 9:00 - 12:30 -> (540,750)
        (13 * 60, 13 * 60 + 30),                    # 13:00 - 13:30 -> (780,810)
        (14 * 60, 16 * 60 + 30)                     # 14:00 - 16:30 -> (840,990)
    ],
    "Tuesday": [
        (9 * 60, 10 * 60 + 30),                     # 9:00 - 10:30 -> (540,630)
        (11 * 60 + 30, 12 * 60 + 30),               # 11:30 - 12:30 -> (690,750)
        (13 * 60, 13 * 60 + 30),                    # 13:00 - 13:30 -> (780,810)
        (15 * 60, 16 * 60),                         # 15:00 - 16:00 -> (900,960)
        (16 * 60 + 30, 17 * 60)                     # 16:30 - 17:00 -> (990,1020)
    ],
    "Wednesday": [
        (9 * 60, 10 * 60),                          # 9:00 - 10:00 -> (540,600)
        (11 * 60, 12 * 60 + 30),                    # 11:00 - 12:30 -> (660,750)
        (13 * 60, 13 * 60 + 30),                    # 13:00 - 13:30 -> (780,810)
        (14 * 60, 14 * 60 + 30),                    # 14:00 - 14:30 -> (840,870)
        (16 * 60 + 30, 17 * 60)                     # 16:30 - 17:00 -> (990,1020)
    ],
    "Thursday": [
        (11 * 60, 12 * 60),                         # 11:00 - 12:00 -> (660,720)
        (13 * 60, 14 * 60),                         # 13:00 - 14:00 -> (780,840)
        (15 * 60, 15 * 60 + 30)                      # 15:00 - 15:30 -> (900,930)
    ],
    "Friday": [
        (10 * 60, 11 * 60),                         # 10:00 - 11:00 -> (600,660)
        (11 * 60 + 30, 12 * 60),                     # 11:30 - 12:00 -> (690,720)
        (12 * 60 + 30, 14 * 60 + 30),                # 12:30 - 14:30 -> (750,870)
        (15 * 60, 15 * 60 + 30),                     # 15:00 - 15:30 -> (900,930)
        (16 * 60, 16 * 60 + 30)                      # 16:00 - 16:30 -> (960,990)
    ]
}

meeting_duration = 60  # in minutes (1 hour)
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

for day in days:
    # Get the busy intervals for each person; if none, use an empty list.
    nicole_busy = nicole_schedule.get(day, [])
    daniel_busy = daniel_schedule.get(day, [])
    
    # Compute free intervals during work hours (9:00 - 17:00)
    nicole_free = get_free_intervals(nicole_busy, 540, 1020)
    daniel_free = get_free_intervals(daniel_busy, 540, 1020)
    
    # Find earliest intersection of free intervals that can fit the meeting
    meeting_slot = find_intersection(nicole_free, daniel_free, meeting_duration)
    
    if meeting_slot:
        start, end = meeting_slot
        # Format the output: day with time range in HH:MM:HH:MM format
        print(f"{day} {minutes_to_time(start)}:{minutes_to_time(end)}")
        break