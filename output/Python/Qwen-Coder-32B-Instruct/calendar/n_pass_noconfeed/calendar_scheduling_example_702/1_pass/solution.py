from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Define participants' busy times
    robert_busy_times = {
        "Monday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                   (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                   (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
        "Tuesday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                    (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
        "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                      (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                      (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                      (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                      (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                      (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
    }
    
    ralph_busy_times = {
        "Monday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                   (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                   (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                    (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                    (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Wednesday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                      (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                      (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                      (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    }
    
    # Meeting duration
    meeting_duration = timedelta(minutes=30)
    
    # Check each day for available slots
    for day in ["Monday", "Tuesday", "Wednesday"]:
        current_time = work_start
        while current_time < work_end - meeting_duration:
            # Check if current time slot is free for both Robert and Ralph
            robert_busy = any(current_time < end and current_time + meeting_duration > start for start, end in robert_busy_times[day])
            ralph_busy = any(current_time < end and current_time + meeting_duration > start for start, end in ralph_busy_times[day])
            
            if not robert_busy and not ralph_busy:
                # If Robert prefers not to have more meetings on Monday, skip this slot if it's on Monday
                if day == "Monday":
                    current_time += timedelta(minutes=30)
                    continue
                
                # Found a suitable time slot
                meeting_start = current_time.strftime("%H:%M")
                meeting_end = (current_time + meeting_duration).strftime("%H:%M")
                print(f"{meeting_start}:{meeting_end} {day}")
                return
            
            # Move to the next 30-minute slot
            current_time += timedelta(minutes=30)

find_meeting_time()