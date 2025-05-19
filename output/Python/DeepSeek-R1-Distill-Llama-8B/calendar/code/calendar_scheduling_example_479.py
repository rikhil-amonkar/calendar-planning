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
    
    # Define the meeting duration
    start_time = datetime.time(9, 0)
    end_time = datetime.time(17, 0)
    
    # Convert schedules to time ranges
    all_busy = []
    for person in schedules:
        busy = []
        for time in person:
            if time[0] > start_time:
                if time[0] - time[1] > datetime.timedelta(hours=1):
                    busy.append((time[0], time[1]))
        all_busy.append(busy)
    
    # Find the latest possible meeting time
    for hour in range(17, 9, -1):
        for minute in range(0, 60):
            start = datetime.time(hour, minute)
            end = datetime.time(hour + 1, minute)
            # Check if all are free
            conflict = False
            for i in range(len(all_busy)):
                # Check if the time is within any busy period
                for b in all_busy[i]:
                    if b[0] <= start < b[1]:
                        conflict = True
                        break
                if conflict:
                    break
            if not conflict:
                return f"{hour:02}:{minute:02}:{hour+1:02}:{minute:02} {day_of_week}"
    
    return "No meeting possible within the given constraints."

# Example usage:
# schedules = {
#     "Evelyn": [],
#     "Joshua": [(11, 30), (12, 30), (13, 30), (14, 30), (16, 30)],
#     "Kevin": [],
#     "Gerald": [],
#     "Jerry": [(9, 30), (10, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30)],
#     "Jesse": [(9, 30), (10, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 30), (15, 0), (15, 30), (16, 30)],
#     "Kenneth": [(10, 30), (12, 30), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 30)]
# }
# print(find_meeting_time(schedules, 1, "Monday"))