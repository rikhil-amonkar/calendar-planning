# Define the work hours and busy times for Carl and Margaret
work_hours_start = 9
work_hours_end = 17
meeting_duration = 1

busy_times = {
    'Carl': {
        'Monday': [(11, 11.5)],
        'Tuesday': [(14.5, 15)],
        'Wednesday': [(10, 11.5), (13, 13.5)],
        'Thursday': [(13.5, 14), (16, 16.5)]
    },
    'Margaret': {
        'Monday': [(9, 10.5), (11, 17)],
        'Tuesday': [(9.5, 12), (13.5, 14), (15.5, 17)],
        'Wednesday': [(9.5, 12), (12.5, 13), (13.5, 14.5), (15, 17)],
        'Thursday': [(10, 12), (12.5, 14), (14.5, 17)]
    }
}

def find_meeting_time():
    days_of_week = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    for day in days_of_week:
        for start in range(work_hours_start, work_hours_end - meeting_duration):
            end = start + meeting_duration
            # Convert to half-hour increments for comparison with busy times
            start_half_hour = start * 2
            end_half_hour = end * 2
            # Check if this slot is free for both participants
            if all(start_half_hour >= b[1] or end_half_hour <= b[0] for b in busy_times['Carl'][day]) and \
               all(start_half_hour >= b[1] or end_half_hour <= b[0] for b in busy_times['Margaret'][day]):
                # If the slot is on Thursday, continue searching unless no other options are available
                if day == 'Thursday':
                    continue
                return f"{start:02}:{int((start % 1) * 60):02}:{end:02}:{int((end % 1) * 60):02} {day}"
    # If no other day is available, return the first valid Thursday slot
    for start in range(work_hours_start, work_hours_end - meeting_duration):
        end = start + meeting_duration
        start_half_hour = start * 2
        end_half_hour = end * 2
        if all(start_half_hour >= b[1] or end_half_hour <= b[0] for b in busy_times['Carl']['Thursday']) and \
           all(start_half_hour >= b[1] or end_half_hour <= b[0] for b in busy_times['Margaret']['Thursday']):
            return f"{start:02}:{int((start % 1) * 60):02}:{end:02}:{int((end % 1) * 60):02} Thursday"

# Find and print the meeting time
print(find_meeting_time())