import datetime

# Define participants' availability
availability = {
    'Jean': {
        'Monday': [(9, 0, 17, 0)],
        'Tuesday': [(9, 0, 11, 30), (16, 30, 17, 0)]
    },
    'Doris': {
        'Monday': [(9, 0, 11, 30), (12, 30, 13, 30), (16, 0, 17, 0)],
        'Tuesday': [(9, 0, 17, 0)]
    }
}

# Meeting duration in hours and minutes
meeting_duration = 30  # in minutes

# Function to find available time slot
def find_meeting_time(availability, meeting_duration, preferred_days):
    for day in preferred_days:
        # Create a list to store busy time slots for both participants
        busy_times = []
        
        # Get busy slots from Jean
        for start_hour, start_minute, end_hour, end_minute in availability['Jean'][day]:
            busy_times.append((datetime.time(start_hour, start_minute),
                               datetime.time(end_hour, end_minute)))
        
        # Get busy slots from Doris
        for start_hour, start_minute, end_hour, end_minute in availability['Doris'][day]:
            busy_times.append((datetime.time(start_hour, start_minute),
                               datetime.time(end_hour, end_minute)))
        
        # Normalize busy times (merging overlapping times)
        busy_times.sort()
        merged_times = []
        
        for start, end in busy_times:
            if not merged_times or merged_times[-1][1] < start:
                merged_times.append((start, end))
            else:
                merged_times[-1] = (merged_times[-1][0], max(merged_times[-1][1], end))
        
        # Check for available time slots
        start_of_day = datetime.time(9, 0)
        end_of_day = datetime.time(17, 0)
        
        current_time = start_of_day
        
        for start, end in merged_times:
            while current_time < start:
                # Check if there's enough time for the meeting before the busy slot
                if (datetime.datetime.combine(datetime.date.today(), start) - 
                    datetime.datetime.combine(datetime.date.today(), current_time)).seconds / 60 >= meeting_duration:
                    meeting_start = current_time
                    meeting_end = (datetime.datetime.combine(datetime.date.today(), current_time) + 
                                   datetime.timedelta(minutes=meeting_duration)).time()
                    return day, meeting_start, meeting_end
                current_time = (datetime.datetime.combine(datetime.date.today(), current_time) + 
                                datetime.timedelta(minutes=30)).time()  # Increment time by 30 minutes
            current_time = max(current_time, end)  # Set current time to the end of the busy slot

        # Check after the last busy slot to the end of the day
        if (datetime.datetime.combine(datetime.date.today(), end_of_day) - 
            datetime.datetime.combine(datetime.date.today(), current_time)).seconds / 60 >= meeting_duration:
            meeting_start = current_time
            meeting_end = (datetime.datetime.combine(datetime.date.today(), current_time) + 
                           datetime.timedelta(minutes=meeting_duration)).time()
            return day, meeting_start, meeting_end

# Preferred days for the meeting
preferred_days = ['Monday', 'Tuesday']

# Finding meeting time
day, meeting_start, meeting_end = find_meeting_time(availability, meeting_duration, preferred_days)
print(f'{meeting_start.strftime("%H:%M")}:{meeting_end.strftime("%H:%M")} {day}')