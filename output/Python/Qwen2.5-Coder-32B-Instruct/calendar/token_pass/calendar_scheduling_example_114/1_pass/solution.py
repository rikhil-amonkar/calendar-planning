def find_meeting_time(participants, meeting_duration, work_start=9, work_end=17):
    from datetime import datetime, timedelta
    
    # Define the work hours in minutes from 00:00
    work_start_minutes = work_start * 60
    work_end_minutes = work_end * 60
    
    # Create a time grid for each half-hour slot within work hours
    time_grid = [True] * ((work_end - work_start) * 2)
    
    # Mark busy slots on the time grid
    for participant in participants:
        for busy_start, busy_end in participant['busy']:
            start_minutes = busy_start.hour * 60 + busy_start.minute
            end_minutes = busy_end.hour * 60 + busy_end.minute
            start_index = (start_minutes - work_start_minutes) // 30
            end_index = (end_minutes - work_start_minutes) // 30
            for i in range(start_index, end_index):
                if 0 <= i < len(time_grid):
                    time_grid[i] = False
    
    # Find the first available slot of the required duration
    duration_slots = meeting_duration * 2  # Convert duration to half-hour slots
    for i in range(len(time_grid) - duration_slots + 1):
        if all(time_grid[i:i + duration_slots]):
            start_time_minutes = work_start_minutes + i * 30
            end_time_minutes = start_time_minutes + duration_slots * 30
            start_time = datetime.strptime(f"{start_time_minutes // 60}:{start_time_minutes % 60}", "%H:%M")
            end_time = datetime.strptime(f"{end_time_minutes // 60}:{end_time_minutes % 60}", "%H:%M")
            return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}", participants[0]['day']
    
    return None

# Define participants' schedules
participants = [
    {'name': 'Stephanie', 'day': 'Monday', 'busy': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                                                   (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]},
    {'name': 'Cheryl', 'day': 'Monday', 'busy': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                                                 (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                                                 (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                                                 (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]},
    {'name': 'Bradley', 'day': 'Monday', 'busy': [(datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
                                                  (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                                                  (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                                                  (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                                                  (datetime.strptime('15:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]},
    {'name': 'Steven', 'day': 'Monday', 'busy': [(datetime.strptime('9:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                                                 (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                                                 (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]}
]

meeting_duration = 1  # Meeting duration in hours
result = find_meeting_time(participants, meeting_duration)

if result:
    print(f"Meeting time: {result[0]} on {result[1]}")
else:
    print("No suitable time found.")