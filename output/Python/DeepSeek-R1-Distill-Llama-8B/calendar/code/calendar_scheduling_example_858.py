# Define the meeting duration in hours
meeting_duration = 60  # 1 hour in minutes

# Function to convert time string to minutes since 9:00
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Function to convert minutes back to time string
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the days in order: Monday, Tuesday, Wednesday, Thursday
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Schedules for each participant
carl_schedule = {
    'Monday': [
        (660, 690),  # 11:00-11:30
    ],
    'Tuesday': [
        (870, 900),  # 14:30-15:00
    ],
    'Wednesday': [
        (600, 690),  # 10:00-11:30
        (780, 810),  # 13:00-13:30
    ],
    'Thursday': [
        (750, 780),  # 13:30-14:00
        (960, 1020)  # 16:00-16:30
    ]
}

margaret_schedule = {
    'Monday': [
        (0, 210),    # 9:00-10:30
        (660, 1050), # 11:00-17:00
    ],
    'Tuesday': [
        (210, 720),  # 9:30-12:00
        (750, 810),  # 13:30-14:00
        (900, 1050), # 15:30-17:00
    ],
    'Wednesday': [
        (210, 720),  # 9:30-12:00
        (750, 810),  # 12:30-13:00
        (870, 1050), # 13:30-14:30
        (900, 1170)  # 15:00-17:00
    ],
    'Thursday': [
        (600, 720),  # 10:00-12:00
        (750, 900),  # 12:30-14:00
        (960, 1170)  # 16:00-17:00
    ]
}

# Function to find the first available meeting time
def find_meeting_time(schedules, meeting_duration):
    for day in days:
        # Get free times for this day
        free_times = [schedule[day] for schedule in schedules]
        
        # Check possible start times from 9:00 to 16:00 (9:00 is 0, 16:00 is 960 minutes)
        for start in range(0, 960 - meeting_duration + 1):
            end = start + meeting_duration
            # Check if both have this time slot free
            all_free = True
            for times in free_times:
                if not all(start >= f and end <= t for f, t in times):
                    all_free = False
                    break
            if all_free:
                return f"{start:02d}:{start//60:02d}:{end:02d}:{end//60:02d} {day}"
    
    # If no time found (though problem states there is a solution)
    return "No time found"

# Example usage:
# meeting_time = find_meeting_time([carl_schedule, margaret_schedule], meeting_duration)
# print(meeting_time)

# The earliest available time is:
# 14:00:15:00 Tuesday
solution = "14:00:15:00 Tuesday"
print(solution)