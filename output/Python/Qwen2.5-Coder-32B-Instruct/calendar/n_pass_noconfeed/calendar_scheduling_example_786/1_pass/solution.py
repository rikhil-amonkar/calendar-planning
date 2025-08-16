from datetime import datetime, timedelta

# Define the available days and time range
available_days = ['Monday', 'Tuesday', 'Wednesday']
start_time = datetime.strptime('09:00', '%H:%M')
end_time = datetime.strptime('17:00', '%H:%M')
meeting_duration = timedelta(minutes=30)

# Define the busy times for Amy and Pamela
amy_busy_times = {
    'Wednesday': [(datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                  (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M'))]
}

pamela_busy_times = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                 (datetime.strptime('11:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                  (datetime.strptime('10:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                    (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                    (datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                    (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                    (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

def is_time_slot_free(busy_times, start, end):
    for busy_start, busy_end in busy_times:
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

def find_meeting_time():
    for day in available_days:
        current_time = start_time
        while current_time + meeting_duration <= end_time:
            amy_busy = amy_busy_times.get(day, [])
            pamela_busy = pamela_busy_times.get(day, [])
            if is_time_slot_free(amy_busy, current_time, current_time + meeting_duration) and \
               is_time_slot_free(pamela_busy, current_time, current_time + meeting_duration):
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
            current_time += timedelta(minutes=15)
    return None, None

meeting_time, meeting_day = find_meeting_time()
print(f"{meeting_time}:{meeting_day}")