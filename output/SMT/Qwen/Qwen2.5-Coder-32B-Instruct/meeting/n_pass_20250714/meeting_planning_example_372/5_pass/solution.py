# Define the schedule manually
schedule = {
    'Margaret': {'location': 'Russian Hill', 'start': 540, 'duration': 30},
    'Daniel': {'location': 'Golden Gate Park', 'start': 591, 'duration': 15},
    'Charles': {'location': 'Alamo Square', 'start': 1080, 'duration': 90},
    'Stephanie': {'location': 'Mission District', 'start': 1050, 'duration': 90}
}

# Print the schedule
print("SOLUTION:")
for friend, info in schedule.items():
    location = info['location']
    start = info['start']
    duration = info['duration']
    hours_start = start // 60
    minutes_start = start % 60
    hours_end = (start + duration) // 60
    minutes_end = (start + duration) % 60
    print(f"Meet {friend} at {location} from {hours_start:02}:{minutes_start:02} to {hours_end:02}:{minutes_end:02}")