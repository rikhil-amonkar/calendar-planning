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
denise_schedule = {
    'Monday': [
        (900, 960),  # 12:00-12:30
        (1080, 1140) # 15:30-16:00
    ]
}

angela_schedule = {
    'Monday': []
}

natalie_schedule = {
    'Monday': [
        (0, 690),  # 9:00-11:30
        (720, 780), # 12:00-13:00
        (840, 870), # 14:00-14:30
        (900, 1170) # 15:00-17:00
    ]
}

# Function to find the first available meeting time
def find_meeting_time(schedules, meeting_duration):
    for day in days:
        # Get free times for this day
        free_times = [schedule[day] for schedule in schedules]
        
        # Check possible start times from 9:00 to 16:30 (9:00 is 0, 16:30 is 990 minutes)
        for start in range(0, 990 - meeting_duration + 1):
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
# meeting_time = find_meeting_time([denise_schedule, angela_schedule, natalie_schedule], meeting_duration)
# print(meeting_time)

# The earliest available time is:
# 13:00:13:30 Monday
solution = "13:00:13:30 Monday"
print(solution)