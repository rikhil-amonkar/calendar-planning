#!/usr/bin/env python3
def time_to_minutes(time_str):
    """Converts HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to HH:MM string."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_list, work_start, work_end):
    """Given a sorted list of busy intervals (in minutes), compute free time intervals
       between work_start and work_end."""
    free = []
    current = work_start
    # busy_list is assumed to be a list of tuples (start, end) in minutes
    busy_list = sorted(busy_list, key=lambda x: x[0])
    for b in busy_list:
        if b[0] > current:
            free.append((current, b[0]))
        current = max(current, b[1])
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2, duration):
    """Return a list of intersecting intervals that are at least 'duration' minutes long."""
    intersections = []
    for int1 in intervals1:
        for int2 in intervals2:
            start = max(int1[0], int2[0])
            end = min(int1[1], int2[1])
            if end - start >= duration:
                intersections.append((start, end))
    # sort by start time
    intersections.sort(key=lambda x: x[0])
    return intersections

# Define working hours in minutes (9:00 to 17:00)
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 30  # minutes

# Busy schedules for each participant (times are given as strings in HH:MM format)
# Daniel's busy intervals per day
daniel_schedule = {
    "Monday": [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Tuesday": [("11:00", "12:00"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Wednesday": [("09:00", "10:00"), ("14:00", "14:30")],
    "Thursday": [("10:30", "11:00"), ("12:00", "13:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Friday": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:30", "17:00")]
}

# Bradley's busy intervals per day
bradley_schedule = {
    "Monday": [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:00", "15:00")],
    "Tuesday": [("10:30", "11:00"), ("12:00", "13:00"), ("13:30", "14:00"), ("15:30", "16:30")],
    "Wednesday": [("09:00", "10:00"), ("11:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")],
    "Thursday": [("09:00", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Friday": [("09:00", "09:30"), ("10:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:30")]
}

# Convert schedule times from HH:MM strings to minutes
def convert_schedule(schedule):
    converted = {}
    for day, intervals in schedule.items():
        converted[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]
    return converted

daniel_busy = convert_schedule(daniel_schedule)
bradley_busy = convert_schedule(bradley_schedule)

# Personal day preferences:
# Daniel: prefers NOT to meet on Wednesday and Thursday.
# Bradley: does NOT want to meet on Monday and Friday.
# Additionally, Bradley does not want Tuesday meetings before 12:00.

# Define all weekdays in order
weekdays = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Function to check and return effective working hours for a person on a given day
def effective_working_hours(person, day):
    # default working hours for everyone are 09:00-17:00
    start = WORK_START
    end = WORK_END
    # Apply Bradley's Tuesday constraint (no meetings before 12:00)
    if person == "Bradley" and day == "Tuesday":
        start = max(start, time_to_minutes("12:00"))
    return start, end

# Main search for a meeting slot that works for both participants
meeting_found = False

for day in weekdays:
    # Apply day preference constraints:
    # Daniel does not want Wednesday or Thursday.
    if day in ["Wednesday", "Thursday"]:
        continue
    # Bradley does not want Monday or Friday.
    if day in ["Monday", "Friday"]:
        continue

    # At this point, the only day left is Tuesday based on the preferences.
    # Get effective working hours for each participant
    daniel_start, daniel_end = effective_working_hours("Daniel", day)
    bradley_start, bradley_end = effective_working_hours("Bradley", day)
    
    # Compute free intervals for Daniel
    daniel_free = get_free_intervals(daniel_busy.get(day, []), daniel_start, daniel_end)
    # Compute free intervals for Bradley
    bradley_free = get_free_intervals(bradley_busy.get(day, []), bradley_start, bradley_end)
    
    # Compute the intersections of free intervals that are long enough for the meeting
    common_free = intersect_intervals(daniel_free, bradley_free, MEETING_DURATION)
    
    if common_free:
        # Choose the earliest start time from the first available intersection
        meeting_start = common_free[0][0]
        meeting_end = meeting_start + MEETING_DURATION
        # Output in the required format: Day and time range HH:MM:HH:MM
        print(f"{day} {{{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}}}")
        meeting_found = True
        break

if not meeting_found:
    print("No available meeting slot found.")