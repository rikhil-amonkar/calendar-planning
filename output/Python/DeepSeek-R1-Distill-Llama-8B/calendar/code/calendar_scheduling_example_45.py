import datetime

def find_meeting_time(schedules, duration, day_of_week):
    # Convert day of week to Monday
    if day_of_week == 'Tuesday':
        day = datetime.date.weekday(datetime.date.today()) + 1
    else:
        day = datetime.date.weekday(datetime.date.today())
    
    # Check if today is the correct day
    if datetime.date.today().weekday() != day:
        return "No meeting possible on the specified day."
    
    # Define the work hours
    start_time = datetime.time(9, 0)
    end_time = datetime.time(17, 0)
    
    # Function to check if a time is within a busy period
    def is_busy(person, time):
        for period in person:
            if period[0] <= time < period[1]:
                return True
        return False
    
    # Convert schedules to time ranges
    all_busy = [person for person in schedules]
    
    # Check each day from earliest to latest
    for day in day_of_week:
        day = datetime.date.fromisoformat(day)
        if day < datetime.date.today():
            continue
        
        # Check each possible time slot
        for hour in range(17, 9, -1):
            for minute in range(0, 60):
                start = datetime.time(hour, minute)
                end = start + datetime.timedelta(hours=duration)
                
                # Check if the time is within work hours
                if end > end_time:
                    continue
                
                # Check if all are free
                conflict = False
                for person in all_busy:
                    if is_busy(person, start):
                        conflict = True
                        break
                if conflict:
                    continue
                
                # Return the earliest possible time
                return f"{hour:02}:{minute:02}:{end.hour:02}:{end.minute:02} {day.weekday():strftime('%A', day)}"
    
    return "No meeting possible within the given constraints."

# Example usage:
# schedules = {
#     "Andrew": [],
#     "Grace": [],
#     "Samuel": [
#         (datetime.time(9, 0), datetime.time(10, 30)),
#         (datetime.time(11, 30), datetime.time(12, 0)),
#         (datetime.time(13, 0), datetime.time(13, 30)),
#         (datetime.time(14, 0), datetime.time(16, 0)),
#         (datetime.time(16, 30), datetime.time(17, 0))
#     ]
# }
# print(find_meeting_time(schedules, datetime.timedelta(hours=0.5), ["Monday"]))