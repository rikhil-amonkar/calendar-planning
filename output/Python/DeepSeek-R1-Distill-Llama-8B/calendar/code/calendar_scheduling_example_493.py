from datetime import time as Time

def find_meeting_time():
    # Define the participants and their schedules
    participants = {
        'Tyler': ('09:00', '17:00'),
        'Kelly': ('09:00', '17:00'),
        'Stephanie': (
            ('11:00', '11:30'),
            ('14:30', '15:00')
        ),
        'Hannah': ('09:00', '17:00'),
        'Joe': (
            ('09:00', '09:30'),
            ('10:00', '12:00'),
            ('12:30', '13:00'),
            ('14:00', '17:00')
        ),
        'Diana': (
            ('09:00', '10:30'),
            ('11:30', '12:00'),
            ('13:00', '14:00'),
            ('14:30', '15:30'),
            ('16:00', '17:00')
        ),
        'Deborah': (
            ('09:00', '10:00'),
            ('10:30', '12:00'),
            ('12:30', '13:00'),
            ('13:30', '14:00'),
            ('14:30', '15:30'),
            ('16:00', '16:30')
        )
    }

    # Convert time strings to minutes since 09:00
    def to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Convert each participant's schedule to a list of busy intervals
    busy_times = {}
    for name, schedule in participants.items():
        times = []
        for start, end in schedule:
            start_min = to_minutes(start)
            end_min = to_minutes(end)
            times.append((start_min, end_min))
        busy_times[name] = times

    # Function to check if a time is busy for a participant
    def is_busy(name, time_min):
        for start, end in busy_times[name]:
            if start <= time_min < end:
                return True
        return False

    # The meeting duration is 30 minutes
    duration = 30

    # Iterate through possible start times from 09:00 to 16:30
    for start_h in range(9, 17):
        for start_m in range(0, 60):
            current_time = start_h * 60 + start_m
            end_time = current_time + duration

            # Check if end_time is within the day (09:00 to 17:00)
            if end_time >= 17 * 60:
                continue

            # Check if everyone is free at current_time
            all_free = True
            for name in participants:
                if is_busy(name, current_time):
                    all_free = False
                    break
            if all_free:
                # Format the time and return
                return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d} {day_of_week}"

    # If no slot found (though problem states a solution exists)
    return "No suitable time found"

# Determine the day of the week (Monday)
day_of_week = "Monday"

# Run the function and print the result
print(find_meeting_time())