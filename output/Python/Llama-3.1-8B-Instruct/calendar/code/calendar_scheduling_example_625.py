from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    available_time = []
    for time in [start_time + timedelta(hours=i) for i in range((end_time - start_time).seconds // 3600 + 1)]:
        time_str = time.strftime('%H:%M')
        if all(time_str not in schedule for schedule in schedules.values()):
            available_time.append(time_str)
    return available_time

def schedule_meeting(meeting_duration, start_time, end_time, schedules, constraints):
    available_times = []
    for day in [start_time + timedelta(days=i) for i in range((end_time - start_time).days + 1)]:
        available_times.extend(find_available_time(day, day + timedelta(hours=17), schedules))
    
    if available_times:
        best_time = max(available_times, key=lambda x: x.split(':')[-1])
        best_start_time = datetime.strptime(best_time, '%H:%M')
        best_end_time = best_start_time + timedelta(hours=meeting_duration)
        
        # Check the constraint that Harold would like to avoid more meetings on Monday
        if best_start_time.strftime('%A') == 'Monday':
            return None, None, None
        
        # Check the constraint that Harold would like to avoid meetings on Tuesday before 14:30
        if best_start_time.strftime('%A') == 'Tuesday' and best_start_time.hour < 14:
            return None, None, None
        
        return best_start_time.strftime('%H:%M'), best_end_time.strftime('%H:%M'), best_start_time.strftime('%A')
    else:
        return None, None, None

# Define the schedules
schedules = {
    'Jeffrey': [],
    'Harold': [['09:00', '10:00'], ['10:30', '17:00'], ['09:00', '09:30'], ['10:30', '11:30'], ['12:30', '13:30'], ['14:30', '15:30'], ['16:00', '17:00']]
}

# Define the meeting duration and start time
meeting_duration = 0.5
start_time = datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=29)
end_time = start_time + timedelta(days=2)

# Find the available time
start_time_str, end_time_str, day_of_week = schedule_meeting(meeting_duration, start_time, end_time, schedules, {'Harold': lambda x: x!= 'Monday' and x.hour >= 14})

# Print the result
if start_time_str and end_time_str:
    print(f"Day: {day_of_week}, Time: {start_time_str}:{end_time_str}")
else:
    print("No available time found.")