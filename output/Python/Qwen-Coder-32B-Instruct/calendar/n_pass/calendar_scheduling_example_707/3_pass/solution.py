from datetime import datetime, timedelta

def find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, available_days):
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in available_days:
        ryan_busy = ryan_schedule[day]
        adam_busy = adam_schedule[day]
        
        # Adjust start and end of day for Monday based on the constraint
        if day == "Monday":
            start_of_day = datetime.strptime(f"09:00 {day}", "%H:%M %A")
            end_of_day = datetime.strptime(f"14:30 {day}", "%H:%M %A")
        else:
            start_of_day = datetime.strptime(f"09:00 {day}", "%H:%M %A")
            end_of_day = datetime.strptime(f"17:00 {day}", "%H:%M %A")
        
        current_time = start_of_day
        
        while current_time + meeting_duration <= end_of_day:
            if all(current_time < busy_start or current_time + meeting_duration > busy_end for busy_start, busy_end in ryan_busy) and \
               all(current_time < busy_start or current_time + meeting_duration > busy_end for busy_start, busy_end in adam_busy):
                return f"{current_time.strftime('%H:%M')} - {(current_time + meeting_duration).strftime('%H:%M')}", day
            
            current_time += timedelta(minutes=30)

# Define schedules with correct busy period tuples
ryan_schedule = {
    "Monday": [(datetime.strptime("09:30 Monday", "%H:%M %A"), datetime.strptime("10:00 Monday", "%H:%M %A")),
               (datetime.strptime("11:00 Monday", "%H:%M %A"), datetime.strptime("12:00 Monday", "%H:%M %A")),
               (datetime.strptime("13:00 Monday", "%H:%M %A"), datetime.strptime("13:30 Monday", "%H:%M %A")),
               (datetime.strptime("15:30 Monday", "%H:%M %A"), datetime.strptime("16:00 Monday", "%H:%M %A"))],
    "Tuesday": [(datetime.strptime("11:30 Tuesday", "%H:%M %A"), datetime.strptime("12:30 Tuesday", "%H:%M %A")),
                (datetime.strptime("15:30 Tuesday", "%H:%M %A"), datetime.strptime("16:00 Tuesday", "%H:%M %A"))],
    "Wednesday": [(datetime.strptime("12:00 Wednesday", "%H:%M %A"), datetime.strptime("13:00 Wednesday", "%H:%M %A")),
                  (datetime.strptime("15:30 Wednesday", "%H:%M %A"), datetime.strptime("16:00 Wednesday", "%H:%M %A")),
                  (datetime.strptime("16:30 Wednesday", "%H:%M %A"), datetime.strptime("17:00 Wednesday", "%H:%M %A"))]
}

adam_schedule = {
    "Monday": [(datetime.strptime("09:00 Monday", "%H:%M %A"), datetime.strptime("10:30 Monday", "%H:%M %A")),
               (datetime.strptime("11:00 Monday", "%H:%M %A"), datetime.strptime("13:30 Monday", "%H:%M %A")),
               (datetime.strptime("14:00 Monday", "%H:%M %A"), datetime.strptime("16:00 Monday", "%H:%M %A")),
               (datetime.strptime("16:30 Monday", "%H:%M %A"), datetime.strptime("17:00 Monday", "%H:%M %A"))],
    "Tuesday": [(datetime.strptime("09:00 Tuesday", "%H:%M %A"), datetime.strptime("10:00 Tuesday", "%H:%M %A")),
                (datetime.strptime("10:30 Tuesday", "%H:%M %A"), datetime.strptime("15:30 Tuesday", "%H:%M %A")),
                (datetime.strptime("16:00 Tuesday", "%H:%M %A"), datetime.strptime("17:00 Tuesday", "%H:%M %A"))],
    "Wednesday": [(datetime.strptime("09:00 Wednesday", "%H:%M %A"), datetime.strptime("09:30 Wednesday", "%H:%M %A")),
                  (datetime.strptime("10:00 Wednesday", "%H:%M %A"), datetime.strptime("11:00 Wednesday", "%H:%M %A")),
                  (datetime.strptime("11:30 Wednesday", "%H:%M %A"), datetime.strptime("14:30 Wednesday", "%H:%M %A")),
                  (datetime.strptime("15:00 Wednesday", "%H:%M %A"), datetime.strptime("15:30 Wednesday", "%H:%M %A")),
                  (datetime.strptime("16:00 Wednesday", "%H:%M %A"), datetime.strptime("16:30 Wednesday", "%H:%M %A"))]
}

# Available days excluding Wednesday
available_days = ["Monday", "Tuesday"]

# Meeting duration in hours
meeting_duration = 0.5

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, available_days)
print(f"{meeting_time}, {meeting_day}")