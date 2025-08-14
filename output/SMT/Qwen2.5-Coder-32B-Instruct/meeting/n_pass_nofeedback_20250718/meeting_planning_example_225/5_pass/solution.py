# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Sunset District', 'North Beach'): 29,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Alamo Square'): 16,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Alamo Square'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Union Square'): 14,
}

# Define the available times for each person
available_times = {
    'Sarah': (time_in_minutes(16, 0), time_in_minutes(18, 15)),
    'Jeffrey': (time_in_minutes(15, 0), time_in_minutes(22, 0)),
    'Brian': (time_in_minutes(16, 0), time_in_minutes(17, 30)),
}

# Define the minimum meeting times
min_meeting_times = {
    'Sarah': 60,
    'Jeffrey': 75,
    'Brian': 75,
}

# Define the order of meetings
order = ['Brian', 'Jeffrey', 'Sarah']

# Initialize the current time and location
current_time = 0
current_location = 'Sunset District'

# Define the itinerary
itinerary = []

# Function to convert time in minutes to HH:MM format
def format_time(minutes):
    hour = minutes // 60 + 9
    minute = minutes % 60
    return f"{hour:02}:{minute:02}"

# Process each meeting in the order
for person in order:
    start_time = current_time + travel_times[(current_location, 'North Beach' if person == 'Sarah' else 'Union Square' if person == 'Jeffrey' else 'Alamo Square')]
    end_time = start_time + min_meeting_times[person]
    
    # Check if the meeting fits within the available time
    if start_time >= available_times[person][0] and end_time <= available_times[person][1]:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        current_time = end_time
        current_location = 'North Beach' if person == 'Sarah' else 'Union Square' if person == 'Jeffrey' else 'Alamo Square'
    else:
        print("No feasible solution found")
        break

# Print the itinerary
print({"itinerary": itinerary})