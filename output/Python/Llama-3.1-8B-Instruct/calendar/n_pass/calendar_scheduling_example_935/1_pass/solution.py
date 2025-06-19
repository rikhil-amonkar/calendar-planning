from datetime import datetime, timedelta

def find_meeting_time(terry_schedule, frances_schedule, meeting_duration, preferences):
    # Define the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Iterate over the days of the week
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        # Iterate over the hours of the day
        for hour in range(9, 18):
            # Create a datetime object for the current hour
            time = datetime.strptime(f'{hour}:00', '%H:%M')

            # Check if the current hour is available for both Terry and Frances
            if (time + timedelta(minutes=meeting_duration)).time() <= end_time.time():
                if day in terry_schedule and (time.time() >= terry_schedule[day][0].time() and time.time() < terry_schedule[day][-1].time()):
                    continue
                if day in frances_schedule and (time.time() >= frances_schedule[day][0].time() and time.time() < frances_schedule[day][-1].time()):
                    continue
                # Check if Frances wants to avoid meetings on Tuesday
                if day == 'Tuesday' and preferences['avoid_tuesday']:
                    continue
                # If the current hour is available, print the proposed meeting time
                print(f'{day}: {time.strftime("%H:%M")}-{(time + timedelta(minutes=meeting_duration)).strftime("%H:%M")}')
                return

# Define the schedules for Terry and Frances
terry_schedule = {
    'Monday': [datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')],
    'Monday': [datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')],
    'Monday': [datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')],
    'Tuesday': [datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')],
    'Tuesday': [datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')],
    'Tuesday': [datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')],
    'Tuesday': [datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')],
    'Wednesday': [datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')],
    'Wednesday': [datetime.strptime('11:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')],
    'Wednesday': [datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')],
    'Wednesday': [datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')],
    'Wednesday': [datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')],
    'Thursday': [datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')],
    'Thursday': [datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')],
    'Thursday': [datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')],
    'Thursday': [datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')],
    'Friday': [datetime.strptime('9:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')],
    'Friday': [datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')],
    'Friday': [datetime.strptime('13:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')],
    'Friday': [datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')]
}

frances_schedule = {
    'Monday': [datetime.strptime('9:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')],
    'Monday': [datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')],
    'Monday': [datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')],
    'Monday': [datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')],
    'Tuesday': [datetime.strptime('9:00', '%H:%M'), datetime.strptime('9:30', '%H:%M')],
    'Tuesday': [datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')],
    'Tuesday': [datetime.strptime('11:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')],
    'Tuesday': [datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')],
    'Tuesday': [datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:30', '%H:%M')],
    'Wednesday': [datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')],
    'Wednesday': [datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')],
    'Wednesday': [datetime.strptime('11:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')],
    'Wednesday': [datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')],
    'Thursday': [datetime.strptime('11:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')],
    'Thursday': [datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')],
    'Friday': [datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')],
    'Friday': [datetime.strptime('11:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')],
    'Friday': [datetime.strptime('13:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')],
    'Friday': [datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')]
}

# Define the meeting duration and preferences
meeting_duration = 30
preferences = {
    'avoid_tuesday': True
}

find_meeting_time(terry_schedule, frances_schedule, meeting_duration, preferences)