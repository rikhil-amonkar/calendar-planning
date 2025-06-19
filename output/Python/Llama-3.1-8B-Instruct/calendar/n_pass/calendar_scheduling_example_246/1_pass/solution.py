from datetime import datetime, timedelta

def find_available_time(participants, duration):
    # Define the start and end of the workday
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Initialize the best time slot
    best_time = None

    # Iterate over all possible time slots
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, duration):
            time = datetime(year=1, month=1, day=1, hour=hour, minute=minute)
            next_time = time + timedelta(minutes=duration)

            # Check if the time slot is available for all participants
            if all(not (time >= participant['start'] and time < participant['end']) 
                   and not (next_time >= participant['start'] and next_time < participant['end']) 
                   for participant in participants):
                # If this is the first available time slot or it's better than the current best time slot, update the best time slot
                if best_time is None or (time.hour, time.minute) < best_time:
                    best_time = (time.hour, time.minute, next_time.hour, next_time.minute)

    # Return the best time slot and the day of the week
    if best_time is not None:
        return f"{datetime.strptime('Monday', '%A').date() + timedelta(days=best_time[0] - 1)} {datetime.strptime(f'{best_time[0]}:{best_time[1]:02}', '%H:%M')}-{datetime.strptime(f'{best_time[2]}:{best_time[3]:02}', '%H:%M')}"
    else:
        return "No available time slot found"

# Define the participants and their schedules
participants = [
    {'name': 'Jacob','start': datetime.strptime('13:30', '%H:%M'), 'end': datetime.strptime('14:00', '%H:%M'), 'duration': 30},
    {'name': 'Jacob','start': datetime.strptime('14:30', '%H:%M'), 'end': datetime.strptime('15:00', '%H:%M'), 'duration': 30},
    {'name': 'Diana','start': datetime.strptime('9:30', '%H:%M'), 'end': datetime.strptime('10:00', '%H:%M'), 'duration': 30},
    {'name': 'Diana','start': datetime.strptime('11:30', '%H:%M'), 'end': datetime.strptime('12:00', '%H:%M'), 'duration': 30},
    {'name': 'Diana','start': datetime.strptime('13:00', '%H:%M'), 'end': datetime.strptime('13:30', '%H:%M'), 'duration': 30},
    {'name': 'Diana','start': datetime.strptime('16:00', '%H:%M'), 'end': datetime.strptime('16:30', '%H:%M'), 'duration': 30},
    {'name': 'Adam','start': datetime.strptime('9:30', '%H:%M'), 'end': datetime.strptime('10:30', '%H:%M'), 'duration': 60},
    {'name': 'Adam','start': datetime.strptime('11:00', '%H:%M'), 'end': datetime.strptime('12:30', '%H:%M'), 'duration': 90},
    {'name': 'Adam','start': datetime.strptime('15:30', '%H:%M'), 'end': datetime.strptime('16:00', '%H:%M'), 'duration': 30},
    {'name': 'Angela','start': datetime.strptime('9:30', '%H:%M'), 'end': datetime.strptime('10:00', '%H:%M'), 'duration': 30},
    {'name': 'Angela','start': datetime.strptime('10:30', '%H:%M'), 'end': datetime.strptime('12:00', '%H:%M'), 'duration': 90},
    {'name': 'Angela','start': datetime.strptime('13:00', '%H:%M'), 'end': datetime.strptime('15:30', '%H:%M'), 'duration': 210},
    {'name': 'Angela','start': datetime.strptime('16:00', '%H:%M'), 'end': datetime.strptime('16:30', '%H:%M'), 'duration': 30},
    {'name': 'Dennis','start': datetime.strptime('9:00', '%H:%M'), 'end': datetime.strptime('9:30', '%H:%M'), 'duration': 30},
    {'name': 'Dennis','start': datetime.strptime('10:30', '%H:%M'), 'end': datetime.strptime('11:30', '%H:%M'), 'duration': 60},
    {'name': 'Dennis','start': datetime.strptime('13:00', '%H:%M'), 'end': datetime.strptime('15:00', '%H:%M'), 'duration': 120},
    {'name': 'Dennis','start': datetime.strptime('16:30', '%H:%M'), 'end': datetime.strptime('17:00', '%H:%M'), 'duration': 30},
]

# Find the available time slot
print(find_available_time(participants, 30))