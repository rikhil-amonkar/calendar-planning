def time_to_minutes(time_str):
    """Converts a time string in HH:MM format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to a time string in HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def interval_overlaps(start1, end1, start2, end2):
    """Returns True if the intervals [start1, end1) and [start2, end2) overlap."""
    return not (end1 <= start2 or start1 >= end2)

# Define work day bounds (in minutes since midnight)
work_day_start = time_to_minutes("09:00")
work_day_end   = time_to_minutes("17:00")
meeting_duration = 30

# Busy schedules for each participant.
# Each busy interval is a tuple with start and end times (HH:MM format)
busy_schedules = {
    "Judy":      [("13:00", "13:30"), ("16:00","16:30")],
    "Olivia":    [("10:00", "10:30"), ("12:00", "13:00"), ("14:00", "14:30")],
    "Eric":      [],  # free the entire day
    "Jacqueline":[("10:00", "10:30"), ("15:00", "15:30")],
    "Laura":     [("09:00", "10:00"), ("10:30", "12:00"), ("13:00", "13:30"),
                  ("14:30", "15:00"), ("15:30", "17:00")],
    "Tyler":     [("09:00", "10:00"), ("11:00", "11:30"), ("12:30", "13:00"),
                  ("14:00", "14:30"), ("15:30", "17:00")],
    "Lisa":      [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                  ("13:00", "13:30"), ("14:00", "14:30"), ("16:00", "17:00")]
}

# Convert all busy intervals into minutes since midnight for easier calculation.
for person in busy_schedules:
    busy_schedules[person] = [(time_to_minutes(start), time_to_minutes(end)) 
                              for start, end in busy_schedules[person]]

def can_schedule(start_time):
    end_time = start_time + meeting_duration
    # The meeting should be fully within working hours.
    if start_time < work_day_start or end_time > work_day_end:
        return False
    # Check each person's busy intervals for conflict.
    for person, intervals in busy_schedules.items():
        for busy_start, busy_end in intervals:
            if interval_overlaps(start_time, end_time, busy_start, busy_end):
                return False
    return True

def find_meeting_time():
    # Try each minute from work_day_start to work_day_end - meeting_duration
    for start in range(work_day_start, work_day_end - meeting_duration + 1):
        if can_schedule(start):
            return start, start + meeting_duration
    return None, None

start, end = find_meeting_time()
if start is not None:
    meeting_start = minutes_to_time(start)
    meeting_end = minutes_to_time(end)
    print(f"{meeting_start}:{meeting_end} Monday")
else:
    print("No available meeting time found.")