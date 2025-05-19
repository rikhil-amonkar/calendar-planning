from datetime import datetime, timedelta

# Define the availability of Natalie and William
natalie_schedule = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
               (datetime.strptime('10:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
               (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
               (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                (datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                  (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Thursday': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                 (datetime.strptime('11:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                 (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
                 (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
}

william_schedule = {
    'Monday': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
               (datetime.strptime('11:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
                (datetime.strptime('13:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                  (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
                  (datetime.strptime('15:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Thursday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                 (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                 (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                 (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                 (datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
}

# Meeting duration
meeting_duration = timedelta(hours=1)

# Function to find a free time slot
def find_meeting_time(natalie_schedule, william_schedule, meeting_duration):
    for day in natalie_schedule.keys():
        natalie_busy_times = natalie_schedule[day]
        william_busy_times = william_schedule[day]

        combined_busy_times = natalie_busy_times + william_busy_times
        combined_busy_times.sort(key=lambda x: x[0])  # Sort by start time

        free_times = []
        last_end_time = datetime.strptime('09:00', '%H:%M')

        for start, end in combined_busy_times:
            if last_end_time + meeting_duration <= start:
                free_times.append((last_end_time, start))
            last_end_time = max(last_end_time, end)

        # Check for free time slot after last busy period before 17:00
        if last_end_time + meeting_duration <= datetime.strptime('17:00', '%H:%M'):
            free_times.append((last_end_time, datetime.strptime('17:00', '%H:%M')))

        for free_start, free_end in free_times:
            if free_end - free_start >= meeting_duration:
                return day, free_start, free_start + meeting_duration

# Find a suitable meeting time
day, start_time, end_time = find_meeting_time(natalie_schedule, william_schedule, meeting_duration)

# Output the proposed time
print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, {day}")