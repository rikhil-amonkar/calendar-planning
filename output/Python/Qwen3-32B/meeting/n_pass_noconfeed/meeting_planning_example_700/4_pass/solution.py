# Define the travel_time dictionary with durations between locations
travel_time = {
    'Home': {'Office': 30, 'Store': 15},
    'Office': {'Home': 30, 'Store': 20},
    'Store': {'Home': 15, 'Office': 20},
    # Add more locations and durations as needed
}

# Example usage (ensure `current_location` and `friend['location']` are defined)
current_location = 'Home'
friend = {'location': 'Office'}

# Access travel duration
travel_duration = travel_time[current_location][friend['location']]
print(f"Travel duration: {travel_duration} minutes")