def str_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def calculate_free_intervals(busy_intervals, work_start, work_end):
    # sort busy intervals by start time
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def find_common_slot(free_lists, duration):
    # Assume working hours are the same for all, so we try every minute in the working day.
    # Duration is in minutes.
    work_start = 9 * 60
    work_end = 17 * 60
    for start in range(work_start, work_end - duration + 1):
        meeting_slot = (start, start + duration)
        # Check that this meeting slot is completely contained in at least one free interval of each participant.
        if all(any(interval[0] <= meeting_slot[0] and meeting_slot[1] <= interval[1] for interval in free) 
               for free in free_lists):
            return meeting_slot
    return None

# Define working hours (in minutes)
work_start = str_to_minutes("09:00")
work_end = str_to_minutes("17:00")

# Busy schedules for each participant as (start, end) in HH:MM, converted to minutes.
bradley_busy = [(str_to_minutes("09:30"), str_to_minutes("10:00")),
                (str_to_minutes("12:30"), str_to_minutes("13:00")),
                (str_to_minutes("13:30"), str_to_minutes("14:00")),
                (str_to_minutes("15:30"), str_to_minutes("16:00"))]

teresa_busy = [(str_to_minutes("10:30"), str_to_minutes("11:00")),
               (str_to_minutes("12:00"), str_to_minutes("12:30")),
               (str_to_minutes("13:00"), str_to_minutes("13:30")),
               (str_to_minutes("14:30"), str_to_minutes("15:00"))]

elizabeth_busy = [(str_to_minutes("09:00"), str_to_minutes("09:30")),
                  (str_to_minutes("10:30"), str_to_minutes("11:30")),
                  (str_to_minutes("13:00"), str_to_minutes("13:30")),
                  (str_to_minutes("14:30"), str_to_minutes("15:00")),
                  (str_to_minutes("15:30"), str_to_minutes("17:00"))]

christian_busy = [(str_to_minutes("09:00"), str_to_minutes("09:30")),
                  (str_to_minutes("10:30"), str_to_minutes("17:00"))]

# Calculate free intervals for each participant
bradley_free = calculate_free_intervals(bradley_busy, work_start, work_end)
teresa_free = calculate_free_intervals(teresa_busy, work_start, work_end)
elizabeth_free = calculate_free_intervals(elizabeth_busy, work_start, work_end)
christian_free = calculate_free_intervals(christian_busy, work_start, work_end)

# List of free intervals for each participant
free_intervals_list = [bradley_free, teresa_free, elizabeth_free, christian_free]
meeting_duration = 30  # meeting duration in minutes

# Find the earliest common 30-minute slot
meeting_slot = find_common_slot(free_intervals_list, meeting_duration)

if meeting_slot:
    start_time = minutes_to_str(meeting_slot[0])
    end_time = minutes_to_str(meeting_slot[1])
    meeting_day = "Monday"
    # Output format: Day HH:MM:HH:MM
    print(f"{meeting_day} {start_time}:{end_time}")
else:
    print("No common slot found")