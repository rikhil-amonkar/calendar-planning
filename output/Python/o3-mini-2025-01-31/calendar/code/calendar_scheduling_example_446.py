def to_minutes(time_str):
    """Convert HH:MM time string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_time_str(minutes):
    """Convert minutes since midnight to HH:MM time string."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Workday boundaries: 09:00 to 17:00 (in minutes)
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")

# Precomputed free intervals (in minutes) for each participant based on their busy schedules.
# The workday is from 09:00 (540 minutes) to 17:00 (1020 minutes).

schedules = {
    "Megan": [
        (to_minutes("09:30"), to_minutes("10:00")),  # Free between 09:30 and 10:00
        (to_minutes("11:00"), to_minutes("12:00")),  # Free between 11:00 and 12:00
        (to_minutes("12:30"), WORK_END)               # Free between 12:30 and 17:00
    ],
    "Christine": [
        (to_minutes("09:30"), to_minutes("11:30")),  # Free between 09:30 and 11:30
        (to_minutes("12:00"), to_minutes("13:00")),  # Free between 12:00 and 13:00
        (to_minutes("14:00"), to_minutes("15:30")),  # Free between 14:00 and 15:30
        (to_minutes("16:30"), WORK_END)               # Free between 16:30 and 17:00
    ],
    "Gabriel": [
        (WORK_START, WORK_END)                       # Free entire day
    ],
    "Sara": [
        (WORK_START, to_minutes("11:30")),           # Free between 09:00 and 11:30
        (to_minutes("12:00"), to_minutes("14:30")),  # Free between 12:00 and 14:30
        (to_minutes("15:00"), WORK_END)              # Free between 15:00 and 17:00
    ],
    "Bruce": [
        (WORK_START, to_minutes("09:30")),           # Free between 09:00 and 09:30
        (to_minutes("10:00"), to_minutes("10:30")),  # Free between 10:00 and 10:30
        (to_minutes("12:00"), to_minutes("12:30")),  # Free between 12:00 and 12:30
        (to_minutes("14:00"), to_minutes("14:30")),  # Free between 14:00 and 14:30
        (to_minutes("15:00"), to_minutes("15:30")),  # Free between 15:00 and 15:30
        (to_minutes("16:30"), WORK_END)              # Free between 16:30 and 17:00
    ],
    "Kathryn": [
        (WORK_START, to_minutes("10:00")),           # Free between 09:00 and 10:00
        (to_minutes("15:30"), to_minutes("16:00")),  # Free between 15:30 and 16:00
        (to_minutes("16:30"), WORK_END)              # Free between 16:30 and 17:00
    ],
    "Billy": [
        (to_minutes("09:30"), to_minutes("11:00")),  # Free between 09:30 and 11:00
        (to_minutes("11:30"), to_minutes("12:00")),  # Free between 11:30 and 12:00
        (to_minutes("14:00"), to_minutes("14:30")),  # Free between 14:00 and 14:30
        (to_minutes("15:30"), WORK_END)              # Free between 15:30 and 17:00
    ]
}

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap between intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            result.append((start_overlap, end_overlap))
        # Move to the next interval in the list that ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Compute the common free intervals across all participants.
participants = list(schedules.keys())
common_free = schedules[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, schedules[person])

# Required meeting duration in minutes (30 minutes)
MEETING_DURATION = 30
meeting_slot = None
for start, end in common_free:
    if end - start >= MEETING_DURATION:
        meeting_slot = (start, start + MEETING_DURATION)
        break

if meeting_slot:
    start_str = to_time_str(meeting_slot[0])
    end_str = to_time_str(meeting_slot[1])
    day = "Monday"
    # Output in format: HH:MM:HH:MM and the day of the week
    print(f"{day} {start_str}:{end_str}")
else:
    print("No common meeting slot available.")