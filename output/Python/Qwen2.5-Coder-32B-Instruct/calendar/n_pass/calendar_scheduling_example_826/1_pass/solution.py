from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, james_schedule, preferred_days, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert schedules to datetime objects
    def convert_to_datetime(schedule):
        return [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in schedule]
    
    james_schedule = convert_to_datetime(james_schedule)
    
    # Check available times for each day
    for day in preferred_days:
        cheryl_busy = False  # Cheryl is free all day
        for start, end in james_schedule:
            if day in ["Monday", "Tuesday"]:
                if start.time() >= work_start.time() and end.time() <= work_end.time():
                    if not (cheryl_busy or any(start <= t < end for t in [work_start + timedelta(minutes=m) for m in range((end - start).seconds // 60)])):
                        if (end - start).total_seconds() / 60 >= meeting_duration:
                            meeting_start = start
                            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
                            return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day
            elif day == "Wednesday":
                if start.time() >= work_start.time() and end.time() <= work_end.time():
                    if not (cheryl_busy or any(start <= t < end for t in [work_start + timedelta(minutes=m) for m in range((end - start).seconds // 60)])):
                        if (end - start).total_seconds() / 60 >= meeting_duration:
                            meeting_start = start
                            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
                            return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day
            elif day == "Thursday":
                if start.time() >= work_start.time() and end.time() <= work_end.time():
                    if not (cheryl_busy or any(start <= t < end for t in [work_start + timedelta(minutes=m) for m in range((end - start).seconds // 60)])):
                        if (end - start).total_seconds() / 60 >= meeting_duration:
                            meeting_start = start
                            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
                            return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day

# James's schedule
james_schedule = [
    ("09:00", "09:30"), ("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:30", "17:00"),
    ("09:00", "11:00"), ("11:30", "12:00"), ("12:30", "15:30"), ("16:00", "17:00"),
    ("10:00", "11:00"), ("12:00", "13:00"), ("13:30", "16:00"),
    ("09:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")
]

# Preferred days excluding Wednesday and Thursday
preferred_days = ["Monday", "Tuesday"]

# Meeting duration in minutes
meeting_duration = 30

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time({}, james_schedule, preferred_days, meeting_duration)
print(f"{meeting_time}, {meeting_day}")