import json

def convert_to_minutes(time_str):
    """Convert time in 'H:MM' format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_to_time(minutes):
    """Convert minutes since midnight back to 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def calculate_optimal_schedule():
    # Define travel times in minutes
    travel_times = {
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'North Beach'): 29,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'North Beach'): 3,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'North Beach'): 5,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Russian Hill'): 4,
    }

    # Define friends' availability and meeting requirements
    friends = {
        'Anthony': {'location': 'Chinatown', 'available': (convert_to_minutes('13:15'), convert_to_minutes('14:30')), 'duration': 60},
        'Rebecca': {'location': 'Russian Hill', 'available': (convert_to_minutes('19:30'), convert_to_minutes('21:15')), 'duration': 105},
        'Melissa': {'location': 'North Beach', 'available': (convert_to_minutes('8:15'), convert_to_minutes('13:30')), 'duration': 105},
    }

    # Starting point and time
    current_location = 'Sunset District'
    current_time = convert_to_minutes('9:00')
    itinerary = []

    # Try to meet Melissa first due to her early availability
    melissa_start = max(current_time + travel_times[(current_location, friends['Melissa']['location'])], friends['Melissa']['available'][0])
    melissa_end = melissa_start + friends['Melissa']['duration']
    if melissa_end <= friends['Melissa']['available'][1]:
        itinerary.append({
            "action": "meet",
            "location": friends['Melissa']['location'],
            "person": "Melissa",
            "start_time": convert_to_time(melissa_start),
            "end_time": convert_to_time(melissa_end)
        })
        current_location = friends['Melissa']['location']
        current_time = melissa_end
    else:
        print("Cannot meet Melissa within her available time.")
        return {}

    # Next, try to meet Anthony
    anthony_start = max(current_time + travel_times[(current_location, friends['Anthony']['location'])], friends['Anthony']['available'][0])
    anthony_end = anthony_start + friends['Anthony']['duration']
    if anthony_end <= friends['Anthony']['available'][1]:
        itinerary.append({
            "action": "meet",
            "location": friends['Anthony']['location'],
            "person": "Anthony",
            "start_time": convert_to_time(anthony_start),
            "end_time": convert_to_time(anthony_end)
        })
        current_location = friends['Anthony']['location']
        current_time = anthony_end
    else:
        print("Cannot meet Anthony within his available time.")
        return {}

    # Finally, try to meet Rebecca
    rebecca_start = max(current_time + travel_times[(current_location, friends['Rebecca']['location'])], friends['Rebecca']['available'][0])
    rebecca_end = rebecca_start + friends['Rebecca']['duration']
    if rebecca_end <= friends['Rebecca']['available'][1]:
        itinerary.append({
            "action": "meet",
            "location": friends['Rebecca']['location'],
            "person": "Rebecca",
            "start_time": convert_to_time(rebecca_start),
            "end_time": convert_to_time(rebecca_end)
        })
        current_location = friends['Rebecca']['location']
        current_time = rebecca_end
    else:
        print("Cannot meet Rebecca within her available time.")
        return {}

    return {"itinerary": itinerary}

# Calculate and print the optimal schedule
schedule = calculate_optimal_schedule()
print(json.dumps(schedule, indent=2))