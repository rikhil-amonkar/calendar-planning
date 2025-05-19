from datetime import datetime, timedelta

def time_to_minutes(time_str):
    # time_str format: "HH:MM"
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def subtract_busy(free_interval, busy_interval):
    # free_interval and busy_interval are tuples (start, end) in minutes.
    free_start, free_end = free_interval
    busy_start, busy_end = busy_interval
    result = []
    # Case when the busy interval doesn't overlap the free interval:
    if busy_end <= free_start or busy_start >= free_end:
        return [free_interval]
    # If there's a free block before the busy time:
    if busy_start > free_start:
        result.append((free_start, busy_start))
    # If there's a free block after the busy time:
    if busy_end < free_end:
        result.append((busy_end, free_end))
    return result

def subtract_busy_intervals(working_interval, busy_intervals):
    free_intervals = [working_interval]
    for busy in busy_intervals:
        new_free = []
        for interval in free_intervals:
            new_free.extend(subtract_busy(interval, busy))
        free_intervals = new_free
    # sort intervals by start time
    free_intervals.sort(key=lambda x: x[0])
    return free_intervals

def intersect_intervals(interval1, interval2):
    start = max(interval1[0], interval2[0])
    end = min(interval1[1], interval2[1])
    if start < end:
        return (start, end)
    return None

def intersect_free_intervals(free1, free2):
    result = []
    i, j = 0, 0
    while i < len(free1) and j < len(free2):
        inter = intersect_intervals(free1[i], free2[j])
        if inter:
            result.append(inter)
        # Move the pointer with the earlier ending interval
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_slot_in_intervals(intervals, duration):
    for start, end in intervals:
        if end - start >= duration:
            return start, start + duration
    return None

# Meeting parameters
meeting_duration = 30  # minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
working_interval = (work_start, work_end)

# Schedules for participants (each busy interval is a tuple (start, end) in minutes)
# Provided times are within work hours.
schedules = {
    "Monday": {
        "Bobby": [("14:30", "15:00")],
        "Michael": [("09:00", "10:00"), 
                    ("10:30", "13:30"), 
                    ("14:00", "15:00"), 
                    ("15:30", "17:00")]
    },
    "Tuesday": {
        "Bobby": [("09:00", "11:30"), 
                  ("12:00", "12:30"), 
                  ("13:00", "15:00"), 
                  ("15:30", "17:00")],
        "Michael": [("09:00", "10:30"), 
                    ("11:00", "11:30"), 
                    ("12:00", "14:00"), 
                    ("15:00", "16:00"), 
                    ("16:30", "17:00")]
    }
}

def convert_schedule_times(schedule):
    # Convert schedule time strings to minutes tuples
    converted = []
    for start, end in schedule:
        converted.append((time_to_minutes(start), time_to_minutes(end)))
    return converted

# Calculate free intervals for each person per day
available_meeting = None
meeting_day = None

for day in ["Monday", "Tuesday"]:
    # Get free intervals for each participant on this day
    day_schedule = schedules[day]
    free_intervals = {}
    for person, busy_times in day_schedule.items():
        busy_times_min = convert_schedule_times(busy_times)
        free_intervals[person] = subtract_busy_intervals(working_interval, busy_times_min)
    # Intersection of free intervals between Bobby and Michael
    common_free = intersect_free_intervals(free_intervals["Bobby"], free_intervals["Michael"])
    # Look for earliest free slot with required duration
    slot = find_slot_in_intervals(common_free, meeting_duration)
    if slot:
        available_meeting = slot
        meeting_day = day
        break

if available_meeting:
    start_time, end_time = available_meeting
    formatted_start = minutes_to_time(start_time)
    formatted_end = minutes_to_time(end_time)
    # Output in the format "HH:MM:HH:MM" and include the day of the week.
    print(f"{formatted_start}:{formatted_end} {meeting_day}")
else:
    print("No available meeting slot found.")