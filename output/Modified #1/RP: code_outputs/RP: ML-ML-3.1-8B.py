from datetime import datetime, timedelta

# Define the start and end time of the workday
start_time = datetime.strptime('09:00', '%H:%M')
end_time = datetime.strptime('17:00', '%H:%M')

# Define Patrick's busy times
patrick_busy_times = [
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
    (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
    (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
    (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
    (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')),
]

# Function to check if a time slot is available
def is_available(time, busy_times):
    for busy_start, busy_end in busy_times:
        if busy_start < time + timedelta(hours=0.5) and busy_end > time:
            return False
    return True

# Function to find the earliest available time slot
def find_earliest_available_time(start_time, end_time, busy_times):
    current_time = start_time
    while current_time < end_time:
        if is_available(current_time, busy_times):
            return current_time.strftime('%H:%M')
        current_time += timedelta(hours=0.5)
    return None

# Find the earliest available time slot
available_time = find_earliest_available_time(start_time, end_time, patrick_busy_times)

# Print the result
if available_time:
    print(f"The earliest available time slot is: {available_time} - {datetime.strptime(available_time, '%H:%M') + timedelta(hours=0.5).strftime('%H:%M')}")
else:
    print("No available time slot found.")