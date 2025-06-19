from datetime import datetime, timedelta

def schedule_meeting(julie_schedule, ruth_schedule, meeting_duration, day, julie_preference):
    # Define start and end of work hours
    start_hour = 9
    end_hour = 17
    
    # Iterate over each day
    for hour in range(start_hour, end_hour):
        # Iterate over each half hour
        for minute in range(0, 60, 30):
            # Check if Ruth is busy
            ruth_busy = False
            for busy_period in ruth_schedule[day]:
                if busy_period[0] <= hour * 60 + minute <= busy_period[1]:
                    ruth_busy = True
                    break
            
            # Check if Julie is busy
            julie_busy = False
            for busy_period in julie_schedule[day]:
                if busy_period[0] <= hour * 60 + minute <= busy_period[1]:
                    julie_busy = True
                    break
            
            # Check if the time slot meets Julie's preference
            if julie_preference and hour * 60 + minute < 11 * 60 + 30:
                continue
            
            # If the time slot is available for both, return it
            if not ruth_busy and not julie_busy:
                start_time = datetime.strptime(f"{day} {hour}:{minute:02d}", "%A %H:%M")
                end_time = start_time + timedelta(minutes=meeting_duration)
                return f"{start_time.strftime('%H:%M')}-{end_time.strftime('%H:%M')} {day}"

# Define existing schedules
julie_schedule = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": []
}

ruth_schedule = {
    "Monday": [(9*60, 17*60)],
    "Tuesday": [(9*60, 17*60)],
    "Wednesday": [(9*60, 17*60)],
    "Thursday": [(9*60, 11*60), (11.5*60, 14.5*60), (15*60, 17*60)]
}

# Define meeting duration
meeting_duration = 30

# Define day of the week
day = "Thursday"

# Define Julie's preference
julie_preference = True

# Schedule the meeting
proposed_time = schedule_meeting(julie_schedule, ruth_schedule, meeting_duration, day, julie_preference)
if proposed_time:
    print(f"Proposed time: {proposed_time}")
else:
    print("No available time slot found.")