from datetime import time, timedelta
import pandas as pd

# Define the working hours
work_hours_start = time(9, 0)
work_hours_end = time(17, 0)

# Define the busy schedules
schedule_nicole = {
    'Monday': [(time(9, 0), time(9, 30)), (time(13, 0), time(13, 30)), (time(14, 30), time(15, 30))],
    'Tuesday': [(time(9, 0), time(9, 30)), (time(11, 30), time(13, 30)), (time(14, 30), time(15, 30))],
    'Wednesday': [(time(10, 0), time(11, 0)), (time(12, 30), time(15, 0)), (time(16, 0), time(17, 0))]
}

schedule_ruth = {
    'Monday': [(time(9, 0), time(17, 0))],
    'Tuesday': [(time(9, 0), time(17, 0))],
    'Wednesday': [(time(9, 0), time(10, 30)), (time(11, 0), time(11, 30)), 
                  (time(12, 0), time(12, 30)), (time(13, 30), time(15, 30)), (time(16, 0), time(16, 30))]
}

# Define meeting duration
meeting_duration = timedelta(minutes=30)

# Function to find available time
def find_available_time():
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        # Get busy times of both participants
        busy_times_nicole = schedule_nicole[day]
        busy_times_ruth = schedule_ruth[day]
        
        # Merge the busy schedules
        busy_times = busy_times_nicole + busy_times_ruth
        
        # Sort and combine overlapping schedules
        busy_times.sort()
        merged_busy_times = []
        for start, end in busy_times:
            if not merged_busy_times or merged_busy_times[-1][1] < start:
                merged_busy_times.append((start, end))
            else:
                merged_busy_times[-1] = (merged_busy_times[-1][0], max(merged_busy_times[-1][1], end))

        # Check for available slots within working hours
        available_starts = [work_hours_start]
        for start, end in merged_busy_times:
            # Check if there's time before this busy slot
            if available_starts[-1] < start:
                available_starts.append(end)
            # Update latest available start time
            available_starts[-1] = max(available_starts[-1], end)

        available_starts.append(work_hours_end)

        # Now check for meeting time slots
        for i in range(len(available_starts) - 1):
            if available_starts[i + 1] - available_starts[i] >= meeting_duration:
                meeting_start = available_starts[i]
                meeting_end = (datetime.combine(datetime.today(), meeting_start) + meeting_duration).time()
                if day == 'Wednesday' and meeting_end > time(13, 30):
                    continue
                return f"{day}: {meeting_start.strftime('%H:%M')} - {meeting_end.strftime('%H:%M')}"

# Output the available time
print(find_available_time())