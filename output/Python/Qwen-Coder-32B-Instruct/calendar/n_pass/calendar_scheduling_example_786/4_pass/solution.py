from datetime import datetime, timedelta

def find_meeting_time():
    # Define the available days and work hours
    days = ['Tuesday', 'Wednesday']  # Exclude Monday due to unavailability
    work_start = datetime.strptime('09:00', '%H:%M')
    work_end = datetime.strptime('17:00', '%H:%M')
    meeting_duration = timedelta(minutes=30)

    # Define busy times for Amy and Pamela
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

    # Function to check if a time slot is free for all participants
    def is_free(day, start):
        end = start + meeting_duration
        if day == 'Tuesday' and (start < datetime.strptime('09:00', '%H:%M') or end > datetime.strptime('16:00', '%H:%M')):
            return False
        for busy_start, busy_end in amy_busy_times.get(day, []):
            if start < busy_end and end > busy_start:
                return False
        for busy_start, busy_end in pamela_busy_times.get(day, []):
            if start < busy_end and end > busy_start:
                return False
        return True

    # Iterate over each day and possible start times to find a free slot
    for day in days:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            if is_free(day, current_time):
                print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}, {day}")
                return
            current_time += timedelta(minutes=15)  # Check every 15 minutes for better granularity

find_meeting_time()