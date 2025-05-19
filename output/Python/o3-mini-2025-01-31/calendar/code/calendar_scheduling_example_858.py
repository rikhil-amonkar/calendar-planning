from datetime import datetime, timedelta

# Define constants for workday start, workday end (in minutes from midnight)
WORK_START = 9 * 60       # 9:00 in minutes (540)
WORK_END = 17 * 60        # 17:00 in minutes (1020)
MEETING_DURATION = 60     # meeting duration in minutes

# Helper function to convert HH:MM string to minutes
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Helper function to convert minutes to HH:MM string
def minutes_to_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Helper function to merge intervals and then find free slots from busy slots
def get_free_intervals(busy_intervals):
    # busy_intervals assumed sorted by start time and non-overlapping
    free_intervals = []
    start = WORK_START
    for b in busy_intervals:
        b_start, b_end = b
        if start < b_start:
            free_intervals.append((start, b_start))
        start = max(start, b_end)
    if start < WORK_END:
        free_intervals.append((start, WORK_END))
    return free_intervals

# Helper function to intersect two lists of intervals
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # Find overlap if it exists
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        # Move the interval that ends first
        if a_end <= b_end:
            i += 1
        else:
            j += 1
    return result

# Define participant schedules.
# Each schedule is a dictionary where keys are days and values are lists of busy time intervals (in minutes)
# Intervals are represented as tuples (start, end) in minutes.
schedules = {
    "Monday": {
        "Carl": [(time_to_minutes("11:00"), time_to_minutes("11:30"))],
        "Margaret": [(time_to_minutes("09:00"), time_to_minutes("10:30")),
                     (time_to_minutes("11:00"), time_to_minutes("17:00"))]
    },
    "Tuesday": {
        "Carl": [(time_to_minutes("14:30"), time_to_minutes("15:00"))],
        "Margaret": [(time_to_minutes("09:30"), time_to_minutes("12:00")),
                     (time_to_minutes("13:30"), time_to_minutes("14:00")),
                     (time_to_minutes("15:30"), time_to_minutes("17:00"))]
    },
    "Wednesday": {
        "Carl": [(time_to_minutes("10:00"), time_to_minutes("11:30")),
                 (time_to_minutes("13:00"), time_to_minutes("13:30"))],
        "Margaret": [(time_to_minutes("09:30"), time_to_minutes("12:00")),
                     (time_to_minutes("12:30"), time_to_minutes("13:00")),
                     (time_to_minutes("13:30"), time_to_minutes("14:30")),
                     (time_to_minutes("15:00"), time_to_minutes("17:00"))]
    },
    "Thursday": {
        "Carl": [(time_to_minutes("13:30"), time_to_minutes("14:00")),
                 (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        "Margaret": [(time_to_minutes("10:00"), time_to_minutes("12:00")),
                     (time_to_minutes("12:30"), time_to_minutes("14:00")),
                     (time_to_minutes("14:30"), time_to_minutes("17:00"))]
    },
}

# Preferred order of days. Carl prefers to avoid Thursday if possible.
preferred_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

def find_meeting_slot():
    for day in preferred_days:
        # Calculate free intervals for each participant on this day.
        day_schedules = schedules.get(day, {})
        # For each participant, start with full work hours as a free interval, then subtract busy times.
        participant_free = []
        for participant in ["Carl", "Margaret"]:
            busy_times = day_schedules.get(participant, [])
            # Sort busy intervals (they are assumed not overlapping)
            busy_times.sort(key=lambda x: x[0])
            free = get_free_intervals(busy_times)
            participant_free.append(free)
        # Intersect free intervals among all participants
        common_free = participant_free[0]
        for i in range(1, len(participant_free)):
            common_free = intersect_intervals(common_free, participant_free[i])
        # Check if any free interval is long enough for the meeting
        for interval in common_free:
            start, end = interval
            if end - start >= MEETING_DURATION:
                meeting_start = start
                meeting_end = start + MEETING_DURATION
                return day, meeting_start, meeting_end
    return None, None, None

day, start_minutes, end_minutes = find_meeting_slot()

if day:
    start_time = minutes_to_time(start_minutes)
    end_time = minutes_to_time(end_minutes)
    # Output in the requested format: HH:MM:HH:MM and day of the week.
    print(f"Meeting Time: {start_time}:{end_time} on {day}")
else:
    print("No available time slot found.")