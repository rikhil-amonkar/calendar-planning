from datetime import datetime, timedelta

# Define work hours and busy times
work_start = 9
work_end = 17
meeting_duration = 1  # in hours

betty_busy = {
    'Monday': [(10, 10.5), (11.5, 12.5), (16, 16.5)],
    'Tuesday': [(9.5, 10), (10.5, 11), (12, 12.5), (13.5, 15), (16.5, 17)],
    'Wednesday': [(13.5, 14), (14.5, 15)],
    'Friday': [(9, 10), (11.5, 12), (12.5, 13), (14.5, 15)]
}

megan_busy = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 9.5), (10, 10.5), (12, 14), (15, 15.5), (16, 16.5)],
    'Wednesday': [(9.5, 10.5), (11, 11.5), (12.5, 13), (13.5, 14.5), (15.5, 17)],
    'Thursday': [(9, 10.5), (11.5, 14), (14.5, 15), (15.5, 16.5)],
    'Friday': [(9, 17)]
}

def is_time_slot_free(day, start, end, busy_times):
    for busy_start, busy_end in busy_times.get(day, []):
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

def find_meeting_time():
    for day in ['Monday', 'Tuesday', 'Friday']:
        current_time = work_start
        while current_time < work_end - meeting_duration:
            next_time = current_time + meeting_duration
            if is_time_slot_free(day, current_time, next_time, betty_busy) and is_time_slot_free(day, current_time, next_time, megan_busy):
                return f"{current_time:02.0f}:{int((current_time % 1) * 60):02}:{next_time:02.0f}:{int((next_time % 1) * 60):02}", day
            current_time += 0.5  # check every half hour

meeting_time, meeting_day = find_meeting_time()
print(f"{meeting_time} {meeting_day}")