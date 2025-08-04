from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    
    # Define busy times for Russell and Alexander
    russell_busy = {
        "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"))],
        "Tuesday": [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))]
    }
    
    alexander_busy = {
        "Monday": [
            (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
            (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
            (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
        ],
        "Tuesday": [
            (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
            (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
            (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
            (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
        ]
    }
    
    # Meeting duration
    meeting_duration = timedelta(hours=1)
    
    # Check each day
    for day in ["Monday", "Tuesday"]:
        current_time = start_time
        
        while current_time + meeting_duration <= end_time:
            available = True
            
            # Check Russell's availability
            for busy_start, busy_end in russell_busy.get(day, []):
                if busy_start <= current_time < busy_end or busy_start < current_time + meeting_duration <= busy_end:
                    available = False
                    break
            
            # Check Alexander's availability
            for busy_start, busy_end in alexander_busy.get(day, []):
                if busy_start <= current_time < busy_end or busy_start < current_time + meeting_duration <= busy_end:
                    available = False
                    break
            
            # Check Russell's preference not to meet on Tuesday before 13:30
            if day == "Tuesday" and current_time < datetime.strptime("13:30", "%H:%M"):
                available = False
            
            if available:
                print(f"{current_time.strftime('%H:%M')} - {(current_time + meeting_duration).strftime('%H:%M')} on {day}")
                return
            
            # Increment current_time by 30 minutes
            current_time += timedelta(minutes=30)

find_meeting_time()