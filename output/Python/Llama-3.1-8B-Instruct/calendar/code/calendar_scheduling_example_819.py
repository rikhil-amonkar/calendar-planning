from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    available_time = []
    for time in [start_time + timedelta(hours=i) for i in range((end_time - start_time).seconds // 3600 + 1)]:
        time_str = time.strftime('%H:%M')
        if all(time_str not in schedule for schedule in schedules.values()):
            available_time.append(time_str)
    return available_time

def schedule_meeting(meeting_duration, start_time, end_time, schedules):
    available_times = []
    for day in [start_time + timedelta(days=i) for i in range((end_time - start_time).days + 1)]:
        if day.strftime('%A')!= 'Monday' and day.strftime('%A')!= 'Tuesday' and day.strftime('%A')!= 'Wednesday':  # Ruth is busy on Monday, Tuesday, Wednesday
            if day.strftime('%A')!= 'Thursday' or day.hour >= 11:  # Julie would like to avoid more meetings on Thursday before 11:30
                available_times.extend(find_available_time(day, day + timedelta(hours=17), schedules))
    
    if available_times:
        best_time = max(available_times, key=lambda x: x.split(':')[-1])
        best_start_time = datetime.strptime(best_time, '%H:%M')
        best_end_time = best_start_time + timedelta(hours=meeting_duration)
        return best_start_time.strftime('%H:%M'), best_end_time.strftime('%H:%M'), best_start_time.strftime('%A')
    else:
        return None, None, None

# Define the schedules
schedules = {
    'Julie': [],
    'Ruth': [['09:00', '17:00'], ['09:00', '17:00'], ['09:00', '17:00'], ['09:00', '11:00'], ['11:30', '14:30'], ['15:00', '17:00']]
}

# Define the meeting duration and start time
meeting_duration = 0.5
start_time = datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=29)
end_time = start_time + timedelta(days=4)

# Find the available time
start_time_str, end_time_str, day_of_week = schedule_meeting(meeting_duration, start_time, end_time, schedules)

# Print the result
if start_time_str and end_time_str:
    print(f"Day: {day_of_week}, Time: {start_time_str}:{end_time_str}")
else:
    print("No available time found.")