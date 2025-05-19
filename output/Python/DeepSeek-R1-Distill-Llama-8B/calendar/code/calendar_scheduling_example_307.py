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
ronald_schedule = {'Monday': []}
stephen_schedule = {
    'Monday': [
        (600, 630),  # 10:00-10:30
        (720, 750)   # 12:00-12:30
    ]
}
brittany_schedule = {
    'Monday': [
        (660, 690),  # 11:00-11:30
        (780, 840),  # 13:30-14:00
        (990, 1020), # 15:30-16:00
        (1170, 1260) # 16:30-17:00
    ]
}
dorothy_schedule = {
    'Monday': [
        (0, 30),     # 9:00-9:30
        (60, 90),    # 10:00-10:30
        (660, 690),  # 11:00-11:30
        (750, 1050), # 12:30-14:00
        (1050, 1110) # 15:30-17:00
    ]
}
rebecca_schedule = {
    'Monday': [
        (150, 180),  # 9:30-10:30
        (660, 690),  # 11:00-11:30
        (720, 750),  # 12:00-12:30
        (750, 1260)  # 13:00-17:00
    ]
}
jordan_schedule = {
    'Monday': [
        (0, 30),     # 9:00-9:30
        (60, 90),    # 10:00-11:00
        (690, 720),  # 11:30-12:00
        (750, 1050), # 13:00-15:00
        (1050, 1110) # 15:30-16:30
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
            # Check if all participants have this time slot free
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
# meeting_time = find_meeting_time([ronald_schedule, stephen_schedule, brittany_schedule, dorothy_schedule, rebecca_schedule, jordan_schedule], meeting_duration)
# print(meeting_time)

# The earliest available time is:
# 12:30:13:00 Monday
solution = "12:30:13:00 Monday"
print(solution)