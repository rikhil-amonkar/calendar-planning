def find_earliest_available_meeting(start_time, end_time, busy_intervals):
    # Define the working hours
    work_start = datetime.time(9, 0)
    work_end = datetime.time(17, 0)
    
    # Convert busy intervals to time objects
    busy = [datetime.time(x) for x in busy_intervals]
    
    # Check each possible half-hour slot
    for meeting_start in range(work_start, work_end, datetime.timedelta(hours=0.5)):
        meeting_end = meeting_start + datetime.timedelta(hours=0.5)
        # Check if the meeting time is within work hours
        if meeting_start >= work_start and meeting_end <= work_end:
            # Check if Patrick is busy during the meeting time
            is_busy = False
            for b in busy:
                if b >= meeting_start and b < meeting_end:
                    is_busy = True
                    break
            if not is_busy:
                return (meeting_start, meeting_end)
    
    return None

# Sample usage
import datetime

busy_intervals = ['9:00-9:30', '10:30-12:00', '12:30-13:30', '14:00-14:30', '15:00-16:30']
meeting = find_earliest_available_meeting(start_time=datetime.time(9, 0), end_time=datetime.time(17, 0), busy_intervals=busy_intervals)
print(f"Meeting starts at {meeting[0]} and ends at {meeting[1]}")
