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

# Natalie's schedule
natalie_schedule = {
    'Monday': [
        (90, 150), (600, 720), (690, 750), (840, 870), (900, 990), (1050, 1170)
    ],  # Convert the given times to minutes
    'Tuesday': [
        (90, 150), (600, 690), (780, 1050), (840, 1050)
    ],  # ... and so on for each day
    # ... similar structure for other days
}

# William's schedule
william_schedule = {
    'Monday': [
        (150, 330), (690, 1050), (1050, 1140)
    ],
    'Tuesday': [
        (90, 750), (780, 1050), (1050, 1140), (1050, 1140)
    ],
    # ... similar structure for other days
}

# Function to find the first available meeting time
def find_meeting_time(natalie, william, meeting_duration):
    for day in days:
        # Get free times for this day
        n_free = natalie[day]
        w_free = william[day]
        
        # Check possible start times from 9:00 to 16:00 (9:00 is 0, 16:00 is 960 minutes)
        for start in range(0, 960 - meeting_duration + 1):
            end = start + meeting_duration
            # Check if both have this time slot free
            if all(start >= f and end <= t for f, t in n_free) and \
               all(start >= f and end <= t for f, t in w_free):
                return f"{start:02d}:{start//60:02d}:{end:02d}:{end//60:02d} {day}"
    
    # If no time found (though problem states there is a solution)
    return "No time found"

# Example usage:
# meeting_time = find_meeting_time(natalie_schedule, william_schedule, meeting_duration)
# print(meeting_time)