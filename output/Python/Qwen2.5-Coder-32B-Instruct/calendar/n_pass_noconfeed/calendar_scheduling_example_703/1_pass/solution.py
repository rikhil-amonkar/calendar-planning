from datetime import datetime, timedelta

def find_meeting_time(stephanie_schedule, betty_schedule, preferred_days, meeting_duration, stephanie_avoid_day, betty_tuesday_constraint):
    days = ["Monday", "Tuesday", "Wednesday"]
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in preferred_days:
        if day == stephanie_avoid_day:
            continue
        
        stephanie_busy_times = stephanie_schedule[day]
        betty_busy_times = betty_schedule[day]
        
        # Filter out times based on constraints
        if day == "Tuesday":
            betty_busy_times = [time for time in betty_busy_times if time[0] <= betty_tuesday_constraint]
        
        # Combine busy times and sort them
        all_busy_times = sorted(stephanie_busy_times + betty_busy_times, key=lambda x: x[0])
        
        # Find free slots
        start_of_day = datetime.strptime(f"09:00", "%H:%M")
        end_of_day = datetime.strptime(f"17:00", "%H:%M")
        
        current_time = start_of_day
        for busy_time in all_busy_times:
            if current_time < busy_time[0]:
                potential_end_time = current_time + meeting_duration
                if potential_end_time <= busy_time[0] and potential_end_time <= end_of_day:
                    return f"{current_time.strftime('%H:%M')}:{potential_end_time.strftime('%H:%M')}", day
            current_time = max(current_time, busy_time[1])
        
        # Check if there's a slot after the last busy time
        if current_time + meeting_duration <= end_of_day:
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
    
    return None, None

# Define schedules
stephanie_schedule = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M"))]
}

betty_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Constraints
preferred_days = ["Monday", "Tuesday", "Wednesday"]
meeting_duration = 1  # in hours
stephanie_avoid_day = "Monday"
betty_tuesday_constraint = datetime.strptime("12:30", "%H:%M")

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(stephanie_schedule, betty_schedule, preferred_days, meeting_duration, stephanie_avoid_day, betty_tuesday_constraint)

print(meeting_time, meeting_day)