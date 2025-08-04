from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert work hours to minutes since start of the day for easier calculations
    work_start_minutes = work_start.hour * 60 + work_start.minute
    work_end_minutes = work_end.hour * 60 + work_end.minute
    
    # Initialize a list to keep track of available slots
    available_slots = [True] * (work_end_minutes - work_start_minutes)
    
    # Mark unavailable slots based on each person's schedule
    for person_schedule in schedules.values():
        for event in person_schedule:
            start_event = event[0].hour * 60 + event[0].minute - work_start_minutes
            end_event = event[1].hour * 60 + event[1].minute - work_start_minutes
            for i in range(start_event, end_event):
                if 0 <= i < len(available_slots):
                    available_slots[i] = False
    
    # Find a contiguous block of time that fits the meeting duration
    meeting_duration_minutes = meeting_duration.seconds // 60
    for i in range(len(available_slots) - meeting_duration_minutes + 1):
        if all(available_slots[i:i + meeting_duration_minutes]):
            start_time_minutes = i + work_start_minutes
            end_time_minutes = start_time_minutes + meeting_duration_minutes
            start_time = work_start + timedelta(minutes=start_time_minutes)
            end_time = work_start + timedelta(minutes=end_time_minutes)
            return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}", "Monday"
    
    return None, None

# Define the schedules in datetime objects
schedules = {
    'Walter': [],
    'Cynthia': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
                (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Ann': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
            (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
            (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
            (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Catherine': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                  (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                  (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Kyle': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
             (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
             (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
             (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
             (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M'))]
}

# Define meeting duration and work hours
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(schedules, meeting_duration, work_start, work_end)
print(f"{meeting_time}, {day_of_week}")