from datetime import datetime

# Parse time strings into time objects
time_start = datetime.strptime("09:00", "%H:%M").time()
time_end = datetime.strptime("17:00", "%H:%M").time()

# Get today's date
today = datetime.today().date()

# Combine today's date with the parsed time
work_start = datetime.combine(today, time_start)
work_end = datetime.combine(today, time_end)

# Example usage: Calculate duration
duration = work_end - work_start
print(duration)  # Output: 8:00:00