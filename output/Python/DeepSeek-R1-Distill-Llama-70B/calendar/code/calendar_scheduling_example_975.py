def find_meeting_time():
    # Define the work hours in minutes since midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    # Define meeting duration in minutes
    meeting_duration = 60  # 1 hour

    # Nicole's busy intervals
    nicole_busy = {
        "Tuesday": [(16*60, 16*60 + 30)],  # 16:00-16:30
        "Wednesday": [(15*60, 15*60 + 30)],  # 15:00-15:30
        "Friday": [(12*60, 12*60 + 30), (15*60 + 30, 16*60)]  # 12:00-12:30, 15:30-16:00
    }

    # Daniel's busy intervals
    daniel_busy = {
        "Monday": [(9*60, 12*60 + 30), (13*60, 13*60 + 30), (14*60, 16*60 + 30)],  # 9:00-12:30, 13:00-13:30, 14:00-16:30
        "Tuesday": [(9*60, 10*60 + 30), (11*60 + 30, 12*60 + 30), (13*60, 13*60 + 30), 
                    (15*60, 16*60), (16*60 + 30, 17*60)],  # 9:00-10:30, 11:30-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00
        "Wednesday": [(9*60, 10*60), (11*60, 12*60 + 30), (13*60, 13*60 + 30), 
                       (14*60, 14*60 + 30), (16*60 + 30, 17*60)],  # 9:00-10:00, 11:00-12:30, 13:00-13:30, 14:00-14:30, 16:30-17:00
        "Thursday": [(11*60, 12*60), (13*60, 14*60), (15*60, 15*60 + 30)],  # 11:00-12:00, 13:00-14:00, 15:00-15:30
        "Friday": [(10*60, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 14*60 + 30), 
                  (15*60, 15*60 + 30), (16*60, 16*60 + 30)]  # 10:00-11:00, 11:30-12:00, 12:30-14:30, 15:00-15:30, 16:00-16:30
    }

    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    for day in days:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            # Check if Nicole is available
            if day in nicole_busy:
                nicole_available = True
                for busy_start, busy_end in nicole_busy[day]:
                    if current_time < busy_end and current_time + meeting_duration > busy_start:
                        nicole_available = False
                        break
                if not nicole_available:
                    current_time += 30  # Skip to next possible time
                    continue

            # Check if Daniel is available
            if day in daniel_busy:
                daniel_available = True
                for busy_start, busy_end in daniel_busy[day]:
                    if current_time < busy_end and current_time + meeting_duration > busy_start:
                        daniel_available = False
                        break
                if not daniel_available:
                    current_time += 30  # Skip to next possible time
                    continue

            # If both are available, return the time
            start_hour = current_time // 60
            start_minute = current_time % 60
            end_time = current_time + meeting_duration
            end_hour = end_time // 60
            end_minute = end_time % 60
            return f"{day},{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

            current_time += 30  # Check every 30 minutes

    return "No available time found"

# Execute the function
print(find_meeting_time())