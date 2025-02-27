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

# Function to find available times
def find_available_times(start, end, busy_times):
    available_times = []
    current_time = start
    while current_time < end:
        is_available = True
        for busy_start, busy_end in busy_times:
            if busy_start <= current_time < busy_end or busy_start < current_time <= busy_end:
                is_available = False
                break
        if is_available:
            available_times.append((current_time, current_time + timedelta(minutes=30)))
        current_time += timedelta(minutes=30)
    return available_times

# Find available times for Harold and Patrick
available_times = find_available_times(start_time, end_time, patrick_busy_times)

# Print available times
print("Available times:")
for i, (start, end) in enumerate(available_times):
    print(f"{i+1}. {start.strftime('%H:%M')} - {end.strftime('%H:%M')}")
