from datetime import datetime, timedelta

# Define the available time slots for each participant
susan_schedule = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
               (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
               (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
               (datetime.strptime('15:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                (datetime.strptime('12:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                  (datetime.strptime('10:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                  (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
                  (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

sandra_schedule = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:00', '%H:%M')),
               (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
               (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                (datetime.strptime('14:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:00', '%H:%M')),
                  (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                  (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:00', '%H:%M'))]
}

meeting_duration = timedelta(hours=0, minutes=30)

# Function to find common free slot
def find_common_slot(susan_slots, sandra_slots):
    for susan_slot in susan_slots:
        for sandra_slot in sandra_slots:
            start_max = max(susan_slot[0], sandra_slot[0])
            end_min = min(susan_slot[1], sandra_slot[1])
            if start_max + meeting_duration <= end_min:
                return start_max, start_max + meeting_duration
    return None

# Iterate over each day to find a common slot
for day in ['Monday', 'Tuesday', 'Wednesday']:
    if day == 'Tuesday':
        continue  # Susan does not want to meet on Tuesday
    common_slot = find_common_slot(susan_schedule[day], sandra_schedule[day])
    if common_slot:
        start_time = common_slot[0].strftime('%H:%M')
        end_time = common_slot[1].strftime('%H:%M')
        print(f"{start_time}:{end_time} {day}")
        break