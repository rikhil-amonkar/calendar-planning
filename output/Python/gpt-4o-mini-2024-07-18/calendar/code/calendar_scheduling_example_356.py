from datetime import datetime, timedelta

# Define the schedules and constraints
participants = {
    'Katherine': [(datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                  (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M'))],
    'Rebecca': [],
    'Julie': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
              (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
              (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
              (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
    'Angela': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
               (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
               (datetime.strptime('11:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
               (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
               (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Nicholas': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                 (datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                 (datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
                 (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Carl': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
             (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
             (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
             (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
             (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Working hours
start_of_work = datetime.strptime('09:00', '%H:%M')
end_of_work = datetime.strptime('17:00', '%H:%M')

# Generate a list of busy times
busy_times = []
for person, times in participants.items():
    busy_times.extend(times)

# Sort busy times
busy_times.sort()

# Identify free time slots
free_slots = []
last_end = start_of_work

for start, end in busy_times:
    if last_end < start:
        free_slots.append((last_end, start))
    last_end = max(last_end, end)

if last_end < end_of_work:
    free_slots.append((last_end, end_of_work))

# Find a suitable time slot for the meeting
for start, end in free_slots:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = meeting_start + meeting_duration
        if meeting_start.time() >= datetime.strptime('15:00', '%H:%M').time():
            print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
            print("Monday")
            break