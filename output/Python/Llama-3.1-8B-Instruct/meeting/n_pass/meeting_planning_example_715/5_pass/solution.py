# Initialize an empty list to store the schedule
schedule = []

# Define the location and person
location = "Office"
person = "John"

# Define the minimum meeting time
min_meeting_time = 30

# Define the location to meet (loc)
loc = "Home"

# Define a custom function to add minutes to a time
def add_minutes(location, time):
    """
    Add minutes to a time.

    Args:
        location (str): The location where the time is being added.
        time (int): The time in minutes.

    Returns:
        int: The time after adding minutes.
    """
    return time + min_meeting_time

# Define a custom function to calculate travel time
def calculate_travel_time(location, loc):
    """
    Calculate travel time between two locations.

    Args:
        location (str): The current location.
        loc (str): The destination location.

    Returns:
        int: The travel time in minutes.
    """
    # For simplicity, assume travel time is 30 minutes for all locations
    return 30

# Calculate the start and end time
start_time = calculate_travel_time(location, loc)
end_time = start_time + min_meeting_time

# Append the schedule to the list
schedule.append({
    "action": "meet",
    "location": location,
    "person": person,
    "start_time": start_time,
    "end_time": end_time
})

# Print the schedule
print(schedule)