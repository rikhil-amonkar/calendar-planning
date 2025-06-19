from datetime import datetime, timedelta

# Define the schedules for Carl and Margaret
class Schedule:
    def __init__(self):
        self.schedules = {
            'Monday': [(9, 10.5), (11, 11.5), (17, 17)],
            'Tuesday': [(9.5, 12), (13.5, 14), (15.5, 17)],
            'Wednesday': [(10, 11.5), (13, 13.5), (15, 17)],
            'Thursday': [(13.5, 14), (16, 16.5), (14.5, 17)]
        }

def find_available_time(schedule, day, duration):
    available_time = []
    for start, end in schedule[day]:
        if start < 18 and end + duration <= 18:
            available_time.append((start, end + duration))
    return available_time

def find_common_time(carl_schedule, margaret_schedule, day, duration):
    carl_available_time = find_available_time(carl_schedule.schedules, day, duration)
    margaret_available_time = find_available_time(margaret_schedule.schedules, day, duration)
    common_time = []
    for carl_time in carl_available_time:
        for margaret_time in margaret_available_time:
            if carl_time[0] >= margaret_time[0] and carl_time[1] <= margaret_time[1]:
                common_time.append((max(carl_time[0], margaret_time[0]), min(carl_time[1], margaret_time[1])))
    return common_time

def find_best_time(carl_schedule, margaret_schedule, day, duration):
    common_time = find_common_time(carl_schedule, margaret_schedule, day, duration)
    if common_time:
        best_time = max(common_time, key=lambda x: x[1] - x[0])
        # Round the start and end times to the nearest half hour
        start = round(best_time[0] * 2) / 2
        end = round(best_time[1] * 2) / 2
        return (start, end)
    else:
        return None

def print_time(time):
    start = datetime.strptime(f'{int(time[0])}:00', '%H:%M')
    end = datetime.strptime(f'{int(time[1])}:00', '%H:%M')
    return f'{start.strftime("%A")}: {start.strftime("%H:%M")} - {end.strftime("%H:%M")}'

def main():
    carl_schedule = Schedule()
    margaret_schedule = Schedule()
    day = 'Monday'
    duration = 1
    best_time = find_best_time(carl_schedule, margaret_schedule, day, duration)
    if best_time:
        print(print_time(best_time))
    else:
        print('No common time found')

if __name__ == '__main__':
    main()