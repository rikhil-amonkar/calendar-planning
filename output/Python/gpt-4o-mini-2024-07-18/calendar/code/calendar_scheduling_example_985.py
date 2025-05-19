from datetime import datetime, timedelta

# Define the time slots for each day
work_hours = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 17)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 17)]
}

# Define the busy schedules for Diane and Matthew
diane_busy = {
    'Monday': [(12, 12.5), (15, 15.5)],
    'Tuesday': [(10, 11), (11.5, 12.5), (16, 17)],
    'Wednesday': [(9, 9.5), (14.5, 15), (16.5, 17)],
    'Thursday': [(15.5, 16.5)],
    'Friday': [(9.5, 11.5), (14.5, 15), (16, 17)]
}

matthew_busy = {
    'Monday': [(9, 10), (10.5, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11), (12, 14.5), (16, 17)],
    'Thursday': [(9, 16)],
    'Friday': [(9, 17)]
}

# Meeting duration
meeting_duration = timedelta(hours=1)

def find_meeting_time():
    for day in work_hours.keys():
        # Calculate free time slots for the day
        free_slots = []
        start_time = work_hours[day][0][0]
        end_time = work_hours[day][0][1]

        # Create a full day's schedule
        full_schedule = [(start_time, end_time)]
        
        # Add busy slots into the schedule
        for busy_slot in diane_busy.get(day, []) + matthew_busy.get(day, []):
            busy_start, busy_end = busy_slot
            new_schedule = []
            
            for (fs, fe) in full_schedule:
                # If there's free time before the busy slot
                if fs < busy_start:
                    new_schedule.append((fs, min(fe, busy_start)))
                # If there's free time after the busy slot
                if fe > busy_end:
                    new_schedule.append((max(fs, busy_end), fe))

            full_schedule = new_schedule

        # Check for a suitable free slot for the meeting
        for (fs, fe) in full_schedule:
            if fe - fs >= meeting_duration.total_seconds() / 3600.0:
                # convert float time back to hh:mm format
                start_hour = int(fs)
                start_minute = int((fs - start_hour) * 60)
                end_hour = start_hour + 1
                end_minute = start_minute
                
                # Return the proposed time
                return f"{day}: {start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02}"

# Call the function to find the meeting time
proposed_time = find_meeting_time()
print(proposed_time)