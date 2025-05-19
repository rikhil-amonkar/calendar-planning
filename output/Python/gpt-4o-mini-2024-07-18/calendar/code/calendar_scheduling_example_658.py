from datetime import datetime, timedelta

def find_meeting_time():
    # Define the schedule constraints
    shirley_schedule = {
        "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                   (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                   (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M"))]
    }
    
    albert_schedule = {
        "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))], 
        "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                    (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    }

    meeting_duration = timedelta(minutes=30)

    # Check for possible meeting times on Monday
    for start_hour in range(9, 17):  # from 9 AM to 5 PM
        start_time = datetime.strptime(f"{start_hour}:00", "%H:%M")
        end_time = start_time + meeting_duration
        
        if end_time.time() <= datetime.strptime("17:00", "%H:%M").time():
            if not is_time_conflicted(start_time, end_time, shirley_schedule["Monday"], albert_schedule["Monday"]):
                return f"Monday {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
    
    # Check for possible meeting times on Tuesday (up to 10:30 preference for Shirley)
    for start_hour in range(9, 11):  # from 9 AM to 10 AM (ending before 10:30)
        start_time = datetime.strptime(f"{start_hour}:00", "%H:%M")
        end_time = start_time + meeting_duration
        
        if end_time.time() <= datetime.strptime("10:30", "%H:%M").time():
            if not is_time_conflicted(start_time, end_time, shirley_schedule["Tuesday"], albert_schedule["Tuesday"]):
                return f"Tuesday {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
    
    return "No available time found"

def is_time_conflicted(start_time, end_time, shirley_slots, albert_slots):
    for slot in shirley_slots + albert_slots:
        if (start_time < slot[1] and end_time > slot[0]):
            return True
    return False

if __name__ == '__main__':
    meeting_time = find_meeting_time()
    print(meeting_time)