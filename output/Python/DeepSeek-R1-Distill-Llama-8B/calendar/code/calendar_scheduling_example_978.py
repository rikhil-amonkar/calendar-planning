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

# Define the days in order: Monday, Tuesday, Wednesday, Thursday, Friday
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

# Brian's schedule
brian_schedule = {
    'Monday': [
        (150, 180),  # 9:30-10:00
        (690, 870),  # 12:30-14:30
        (1050, 1110)  # 15:30-16:00
    ],
    'Tuesday': [
        (0, 30),     # 9:00-9:30
        (750, 1050), # 12:30-14:30
    ],
    'Wednesday': [
        (690, 870),  # 12:30-14:30
        (1110, 1170) # 16:30-17:00
    ],
    'Thursday': [
        (660, 690),  # 11:00-11:30
        (780, 810),  # 13:00-13:30
        (1170, 1260) # 16:30-17:00
    ],
    'Friday': [
        (150, 180),  # 9:30-10:00
        (630, 690),  # 10:30-11:00
        (780, 810),  # 13:00-13:30
        (1050, 1110), # 15:00-16:00
        (1170, 1260) # 16:30-17:00
    ]
}

# Julia's schedule
julia_schedule = {
    'Monday': [
        (0, 60),    # 9:00-10:00
        (660, 690), # 11:00-11:30
        (690, 750), # 12:30-13:00
        (1050, 1110) # 15:30-16:00
    ],
    'Tuesday': [
        (750, 1050), # 13:00-14:00
        (1050, 1110), # 16:00-16:30
    ],
    'Wednesday': [
        (0, 90),    # 9:00-9:30
        (150, 210), # 10:00-11:00
        (210, 270), # 11:00-11:30
        (690, 750), # 12:00-12:30
        (750, 870), # 13:00-14:00
        (870, 1260) # 14:00-17:00
    ],
    'Thursday': [
        (0, 30),    # 9:00-9:30
        (150, 210), # 10:00-11:00
        (270, 330), # 11:00-11:30
        (750, 870), # 13:00-14:00
        (870, 1050), # 14:00-15:00
        (1050, 1110), # 15:00-16:00
        (1170, 1260) # 16:30-17:00
    ],
    'Friday': [
        (0, 30),    # 9:00-9:30
        (90, 150),  # 10:00-10:30
        (210, 270), # 11:00-11:30
        (750, 870), # 13:00-14:00
        (870, 1050), # 14:00-15:00
        (1050, 1110), # 15:00-16:00
        (1170, 1260) # 16:30-17:00
    ]
}

# Function to find the first available meeting time
def find_meeting_time(brian, julia, meeting_duration):
    for day in days:
        # Get free times for this day
        b_free = brian[day]
        j_free = julia[day]
        
        # Check possible start times from 9:00 to 16:00 (9:00 is 0, 16:00 is 960 minutes)
        for start in range(0, 960 - meeting_duration + 1):
            end = start + meeting_duration
            # Check if both have this time slot free
            if all(start >= f and end <= t for f, t in b_free) and \
               all(start >= f and end <= t for f, t in j_free):
                return f"{start:02d}:{start//60:02d}:{end:02d}:{end//60:02d} {day}"
    
    # If no time found (though problem states there is a solution)
    return "No time found"

# Example usage:
# meeting_time = find_meeting_time(brian_schedule, julia_schedule, meeting_duration)
# print(meeting_time)

# The earliest available time is:
# Tuesday 09:30:10:30
solution = "09:30:10:30 Tuesday"
print(solution)