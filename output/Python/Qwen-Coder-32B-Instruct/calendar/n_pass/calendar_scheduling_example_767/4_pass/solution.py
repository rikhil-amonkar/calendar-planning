from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")

    # Define busy times for Martha and Beverly
    martha_busy = {
        "Monday": [(datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Tuesday": [(datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
        "Wednesday": [
            (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
            (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))
        ]
    }

    beverly_busy = {
        "Monday": [
            (datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
            (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
        ],
        "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Wednesday": [
            (datetime.strptime("09:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
            (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
        ]
    }

    # Meeting duration
    meeting_duration = timedelta(hours=1)

    # Find available time slot
    for day in ["Monday", "Tuesday", "Wednesday"]:
        current_time = start_time
        while current_time + meeting_duration <= end_time:
            available = True
            
            # Check Martha's busy times
            for busy_time in martha_busy.get(day, []):
                if current_time < busy_time[1] and current_time + meeting_duration > busy_time[0]:
                    available = False
                    break
            
            # Check Beverly's busy times
            for busy_time in beverly_busy.get(day, []):
                if current_time < busy_time[1] and current_time + meeting_duration > busy_time[0]:
                    available = False
                    break
            
            # If the slot is still available, print it and return
            if available:
                print(f"Available meeting time: {current_time.strftime('%H:%M')} - {(current_time + meeting_duration).strftime('%H:%M')} on {day}")
                return
            
            # Increment current_time to the next potential slot
            current_time += timedelta(minutes=30)
    
    print("No available meeting time found.")

find_meeting_time()