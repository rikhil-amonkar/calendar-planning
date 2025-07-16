# Define excluded_times as an example dictionary
# Each key is a day, and each value is a list of excluded times (in minutes since the start of the day)
excluded_times = {
    'Monday': [540, 1020],  # Example: 9 AM to 17 PM
    'Tuesday': [540, 1020],
    # Add other days and their excluded times as needed
}

# Assuming 'day', 'current_time_minutes', and 'meeting_end_minutes' are defined elsewhere in your code
day = 'Monday'
current_time_minutes = 550  # Example: 9:10 AM
meeting_end_minutes = 600   # Example: 10 AM

# Check if there are any excluded times for the given day
excluded = any(
    start <= current_time_minutes < end or start < meeting_end_minutes <= end
    for start, end in [(ex, ex + 1) for ex in excluded_times.get(day, [])]
)

print("Excluded:", excluded)