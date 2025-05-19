from datetime import datetime, timedelta

# Define work hours and participants' schedules
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Schedules for each participant
schedules = {
    "Gregory": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))],
    "Jonathan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Barbara": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M"))],
    "Jesse": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Alan": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
             (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Nicole": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Catherine": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Function to find a suitable time for the meeting
def find_meeting_time():
    current_time = work_start
    
    while current_time + meeting_duration <= work_end:
        busy_time_intervals = []
        
        for participant, busy_times in schedules.items():
            for busy_start, busy_end in busy_times:
                if busy_start < current_time + meeting_duration and busy_end > current_time:
                    busy_time_intervals.append((busy_start, busy_end))
        
        # Check if the current time slot is free for all participants
        if not busy_time_intervals:
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M"), "Monday"
        
        # Move to the end of the earliest busy time
        current_time = max(busy_end for busy_start, busy_end in busy_time_intervals)
    
    return None

# Get the meeting time
meeting_time = find_meeting_time()

# Output the result
if meeting_time:
    print("{0}:{1}:{2}:{3}".format(meeting_time[0], meeting_time[1], meeting_time[2], meeting_time[2]))
else:
    print("No suitable time found.")