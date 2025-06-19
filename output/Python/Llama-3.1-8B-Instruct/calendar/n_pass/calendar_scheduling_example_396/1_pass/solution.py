from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    available_time = []
    for time in [start_time + timedelta(minutes=i) for i in range((end_time - start_time).seconds // 60 + 1)]:
        if all(time >= schedule[0] and time < schedule[1] for schedule in schedules.values()):
            available_time.append(time)
    return available_time

def schedule_meeting(start_time, end_time, schedules, duration):
    available_times = find_available_time(start_time, end_time, schedules)
    available_times.sort()
    for i in range(len(available_times) - duration):
        time_range = (available_times[i], available_times[i] + timedelta(minutes=duration))
        if all(time_range[0] >= schedule[0] and time_range[1] <= schedule[1] for schedule in schedules.values()):
            return time_range

def main():
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')
    day_of_week = 'Monday'

    schedules = {
        'Andrea': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        'Jack': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')) + (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
        'Madison': (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')) + (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')) + (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')) + (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        'Rachel': (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')) + (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')) + (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')) + (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')) + (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        'Douglas': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')) + (datetime.strptime('12:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')),
        'Ryan': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')) + (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')) + (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
    }

    duration = 30
    meeting_time = schedule_meeting(start_time, end_time, schedules, duration)
    if meeting_time:
        print(f'Time: {meeting_time[0].strftime("%H:%M")} - {meeting_time[1].strftime("%H:%M")}, Day: {day_of_week}')
    else:
        print('No available time found.')

if __name__ == '__main__':
    main()