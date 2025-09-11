# Define the durations dictionary with example data
durations = {
    "Activity 1": 2,   # Example: 2 hours
    "Activity 2": 1.5,  # Example: 1.5 hours
    "Activity 3": 3    # Example: 3 hours
}

# Initialize variables for the schedule
start_time = 0.0
plan = []

# Generate the schedule
for activity, duration in durations.items():
    end_time = start_time + duration
    plan.append((activity, start_time, end_time))
    start_time = end_time

# Print the plan
print("Generated Plan:")
for activity, start, end in plan:
    print(f"- {activity}: {start} to {end} hours")

# Calculate and print the total duration
total_duration = sum(durations.values())
print(f"\nTotal duration: {total_duration} hours")