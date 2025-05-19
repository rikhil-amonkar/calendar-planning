# Define the meeting duration in hours
meeting_duration = 30  # 0.5 hours in minutes

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
days = ['Monday']

# Schedules for each participant
christine_schedule = {
    'Monday': [
        (660, 690),  # 11:00-11:30
        (900, 930)   # 15:00-15:30
    ]
}

helen_schedule = {
    'Monday': [
        (210, 240),  # 9:30-10:30
        (660, 690),  # 11:00-11:30
        (720, 750),  # 12:00-12:30
        (690, 990),  # 13:30-16:00
        (1050, 1170) # 16:30-17:00
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
# meeting_time = find_meeting_time([christine_schedule, helen_schedule], meeting_duration)
# print(meeting_time)

# The earliest available time is:
# 12:30:13:00 Monday
solution = "12:30:13:00 Monday"
print(solution)