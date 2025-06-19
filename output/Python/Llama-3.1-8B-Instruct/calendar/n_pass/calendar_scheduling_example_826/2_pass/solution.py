from datetime import datetime, timedelta

def find_available_time(cheryl_schedule, james_schedule, meeting_duration, preferred_days):
    # Filter schedules to only include preferred days
    james_schedule = {day: slots for day, slots in james_schedule.items() if day in preferred_days}
    
    # Sort days by earliest available time
    days = sorted(james_schedule.keys())
    
    # Iterate over each day
    for day in days:
        # Get available time slots for the day
        available_slots = []
        for slot in james_schedule[day]:
            start, end = slot
            # Convert datetime to time
            start_time = start.time()
            end_time = end.time()
            day_start_time = (datetime.strptime('09:00', '%H:%M') + timedelta(days=days.index(day))).time()
            day_end_time = (datetime.strptime('17:00', '%H:%M') + timedelta(days=days.index(day))).time()
            # Check if the slot starts after the day starts and ends before the day ends
            if start_time >= day_start_time and end_time <= day_end_time:
                available_slots.append((start, end))
        
        # Find the first available time slot that can accommodate the meeting
        for slot in available_slots:
            start, end = slot
            # Check if the meeting can fit in the available slot
            if start + timedelta(minutes=meeting_duration) <= end:
                return f"{day}, {start.strftime('%H:%M')} - {end.strftime('%H:%M')}"

    return "No available time found"

# Example usage
cheryl_schedule = {}
james_schedule = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
              (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
              (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
              (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
              (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                (datetime.strptime('12:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
                (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                  (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
                  (datetime.strptime('13:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Thursday': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                 (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                 (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                 (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
                 (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}
meeting_duration = timedelta(minutes=30)
preferred_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

print(find_available_time(cheryl_schedule, james_schedule, meeting_duration, preferred_days))