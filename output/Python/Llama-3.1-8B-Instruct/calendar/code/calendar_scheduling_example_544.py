from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    available_time = []
    for time in [start_time + timedelta(hours=i) for i in range((end_time - start_time).seconds // 3600 + 1)]:
        time_str = time.strftime('%H:%M')
        if all(time_str not in schedule for schedule in schedules.values()):
            available_time.append(time_str)
    return available_time

def schedule_meeting(meeting_duration, start_time, schedules, constraints):
    end_time = start_time + timedelta(hours=meeting_duration)
    available_times = find_available_time(start_time, end_time, schedules)
    
    if available_times:
        best_time = max(available_times, key=lambda x: x.split(':')[-1])
        best_start_time = datetime.strptime(best_time, '%H:%M')
        best_end_time = best_start_time + timedelta(hours=meeting_duration)
        
        # Check the constraint that Albert cannot meet after 11:00
        if best_start_time.hour > 11:
            return None, None, None
        
        return best_start_time.strftime('%H:%M'), best_end_time.strftime('%H:%M'), best_start_time.strftime('%A')
    else:
        return None, None, None

# Define the schedules
schedules = {
    'Deborah': [],
    'Albert': ['09:00', '10:00', '10:30', '12:00', '15:00', '16:30']
}

# Define the meeting duration and start time
meeting_duration = 0.5
start_time = datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=29)

# Find the available time
start_time_str, end_time_str, day_of_week = schedule_meeting(meeting_duration, start_time, schedules, {'Albert': lambda x: x > 11})

# Print the result
if start_time_str and end_time_str:
    print(f"Day: {day_of_week}, Time: {start_time_str}:{end_time_str}")
else:
    print("No available time found.")