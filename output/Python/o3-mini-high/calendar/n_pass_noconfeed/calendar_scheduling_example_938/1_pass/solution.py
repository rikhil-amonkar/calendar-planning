def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    # sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(busy_intervals, work_start, work_end):
    free = []
    if not busy_intervals:
        return [(work_start, work_end)]
    # Gap before the first busy interval
    if work_start < busy_intervals[0][0]:
        free.append((work_start, busy_intervals[0][0]))
    # Gaps between busy intervals
    for i in range(len(busy_intervals) - 1):
        end_current = busy_intervals[i][1]
        start_next = busy_intervals[i+1][0]
        if end_current < start_next:
            free.append((end_current, start_next))
    # Gap after the last busy interval
    if busy_intervals[-1][1] < work_end:
        free.append((busy_intervals[-1][1], work_end))
    return free

# Define schedules for each participant
# Meeting hours are from 09:00 to 17:00 (inclusive)
schedules = {
    "Monday": {
        "Eugene": [("11:00", "12:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("16:00", "16:30")],
        "Eric":   [("09:00", "17:00")]
    },
    "Tuesday": {
        "Eugene": [],
        "Eric":   [("09:00", "17:00")]
    },
    "Wednesday": {
        "Eugene": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:00")],
        "Eric":   [("09:00", "11:30"), ("12:00", "14:00"), ("14:30", "16:30")]
    },
    "Thursday": {
        "Eugene": [("09:30", "10:00"), ("11:00", "12:30")],
        "Eric":   [("09:00", "17:00")]
    },
    "Friday": {
        "Eugene": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30")],
        "Eric":   [("09:00", "11:00"), ("11:30", "17:00")]
    }
}

meeting_duration = 30  # meeting length in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Function to determine an available meeting slot on a given day
def find_slot_for_day(day, schedules):
    busy_intervals = []
    for person, intervals in schedules[day].items():
        for start_str, end_str in intervals:
            start = time_to_minutes(start_str)
            end = time_to_minutes(end_str)
            busy_intervals.append((start, end))
    merged_busy = merge_intervals(busy_intervals)
    free_intervals = get_free_intervals(merged_busy, work_start, work_end)
    for free_start, free_end in free_intervals:
        if free_end - free_start >= meeting_duration:
            return (free_start, free_start + meeting_duration)
    return None

# Eric prefers to avoid Wednesday. So check non-Wednesday days first.
preferred_days = ["Monday", "Tuesday", "Thursday", "Friday"]
meeting_slot = None
meeting_day = None

for day in preferred_days:
    slot = find_slot_for_day(day, schedules)
    if slot is not None:
        meeting_slot = slot
        meeting_day = day
        break

# If no slot was found in the preferred days, try Wednesday.
if meeting_slot is None:
    day = "Wednesday"
    slot = find_slot_for_day(day, schedules)
    if slot is not None:
        meeting_slot = slot
        meeting_day = day

# Output the meeting time and day in the required format: HH:MM:HH:MM and day.
if meeting_slot:
    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])
    print(f"{meeting_day}, {start_time}:{end_time}")
else:
    print("No available meeting slot found.")