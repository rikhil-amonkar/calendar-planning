import datetime

# Define participants' schedules
danielle_schedule = [(9, 0, 10, 0), (10, 30, 11, 0), (14, 30, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)]
bruce_schedule = [(11, 0, 11, 30), (12, 30, 13, 0), (14, 0, 14, 30), (15, 30, 16, 0)]
eric_schedule = [(9, 0, 9, 30), (10, 0, 11, 0), (11, 30, 13, 0), (14, 30, 15, 30)]

# Define work hours and meeting duration
work_start = (9, 0)
work_end = (17, 0)
meeting_duration = 1  # in hours

# Function to convert schedule to a set of free time intervals
def get_free_time_slots(start, end, schedules):
    free_slots = []
    current_start = start

    for meeting in sorted(schedules):
        if current_start < meeting[:2]:
            free_slots.append((current_start, meeting[:2]))
        current_start = max(current_start, meeting[2:])

    if current_start < end:
        free_slots.append((current_start, end))

    return free_slots

# Get free time slots for each participant
danielle_free = get_free_time_slots(work_start, work_end, danielle_schedule)
bruce_free = get_free_time_slots(work_start, work_end, bruce_schedule)
eric_free = get_free_time_slots(work_start, work_end, eric_schedule)

# Find overlapping time slots that accommodate all participants
def find_meeting_time(danielle_free, bruce_free, eric_free, duration):
    for d_start, d_end in danielle_free:
        for b_start, b_end in bruce_free:
            for e_start, e_end in eric_free:
                start_time = max(d_start, b_start, e_start)
                end_time = start_time + duration
                
                if end_time <= d_end and end_time <= b_end and end_time <= e_end:
                    return start_time, end_time

# Check for overlapping time and calculate
meeting_time = find_meeting_time(danielle_free, bruce_free, eric_free, meeting_duration)

if meeting_time:
    meeting_start = meeting_time[0]
    meeting_end = meeting_time[1]
    day_of_week = "Monday"
    
    # Format the output time
    output = f"{meeting_start[0]:02}:{meeting_start[1]:02}:{meeting_end[0]:02}:{meeting_end[1]:02} - {day_of_week}"
    print(output)