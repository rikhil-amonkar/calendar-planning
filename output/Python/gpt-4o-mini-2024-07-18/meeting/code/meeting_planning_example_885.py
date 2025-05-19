import json
from datetime import datetime, timedelta
import itertools

# Travel times in minutes
travel_times = {
    'Russian Hill': {'Marina District': 8, 'Financial District': 11, 'Alamo Square': 13, 'Golden Gate Park': 19, 'The Castro': 18, 'Bayview': 23, 'Sunset District': 24, 'Haight-Ashbury': 17, 'Nob Hill': 5},
    'Marina District': {'Russian Hill': 7, 'Financial District': 17, 'Alamo Square': 15, 'Golden Gate Park': 16, 'The Castro': 21, 'Bayview': 27, 'Sunset District': 19, 'Haight-Ashbury': 16, 'Nob Hill': 12},
    'Financial District': {'Russian Hill': 11, 'Marina District': 15, 'Alamo Square': 17, 'Golden Gate Park': 26, 'The Castro': 21, 'Bayview': 19, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Nob Hill': 8},
    'Alamo Square': {'Russian Hill': 13, 'Marina District': 15, 'Financial District': 17, 'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16, 'Sunset District': 16, 'Haight-Ashbury': 5, 'Nob Hill': 11},
    'Golden Gate Park': {'Russian Hill': 21, 'Marina District': 18, 'Financial District': 23, 'Alamo Square': 9, 'The Castro': 13, 'Bayview': 22, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Nob Hill': 20},
    'The Castro': {'Russian Hill': 18, 'Marina District': 21, 'Financial District': 21, 'Alamo Square': 8, 'Golden Gate Park': 11, 'Bayview': 19, 'Sunset District': 17, 'Haight-Ashbury': 6, 'Nob Hill': 16},
    'Bayview': {'Russian Hill': 23, 'Marina District': 27, 'Financial District': 19, 'Alamo Square': 16, 'Golden Gate Park': 22, 'The Castro': 19, 'Sunset District': 23, 'Haight-Ashbury': 19, 'Nob Hill': 20},
    'Sunset District': {'Russian Hill': 24, 'Marina District': 21, 'Financial District': 30, 'Alamo Square': 17, 'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 'Haight-Ashbury': 15, 'Nob Hill': 27},
    'Haight-Ashbury': {'Russian Hill': 17, 'Marina District': 17, 'Financial District': 21, 'Alamo Square': 5, 'Golden Gate Park': 7, 'The Castro': 6, 'Bayview': 18, 'Sunset District': 15, 'Nob Hill': 15},
    'Nob Hill': {'Russian Hill': 5, 'Marina District': 11, 'Financial District': 9, 'Alamo Square': 11, 'Golden Gate Park': 17, 'The Castro': 17, 'Bayview': 19, 'Sunset District': 24, 'Haight-Ashbury': 13},
}

# Meeting constraints
meeting_constraints = [
    {'name': 'Mark', 'location': 'Marina District', 'start': '18:45', 'end': '21:00', 'duration': 90},
    {'name': 'Karen', 'location': 'Financial District', 'start': '09:30', 'end': '12:45', 'duration': 90},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': '10:00', 'end': '19:30', 'duration': 90},
    {'name': 'Nancy', 'location': 'Golden Gate Park', 'start': '16:45', 'end': '20:00', 'duration': 105},
    {'name': 'David', 'location': 'The Castro', 'start': '09:00', 'end': '18:00', 'duration': 120},
    {'name': 'Linda', 'location': 'Bayview', 'start': '18:15', 'end': '19:45', 'duration': 45},
    {'name': 'Kevin', 'location': 'Sunset District', 'start': '10:00', 'end': '17:45', 'duration': 120},
    {'name': 'Matthew', 'location': 'Haight-Ashbury', 'start': '10:15', 'end': '15:30', 'duration': 45},
    {'name': 'Andrew', 'location': 'Nob Hill', 'start': '11:45', 'end': '16:45', 'duration': 105}
]

# Function to convert time string to datetime
def convert_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Function to calculate meeting schedule
def calculate_schedule():
    start_time = convert_time('09:00')
    end_time = convert_time('21:00')
    itinerary = []
    current_time = start_time

    # Prioritize meetings based on latest end time
    sorted_constraints = sorted(meeting_constraints, key=lambda x: convert_time(x['end']))

    for constraint in sorted_constraints:
        duration = timedelta(minutes=constraint['duration'])
        meeting_start = latest_start_time = convert_time(constraint['start'])
        meeting_end = convert_time(constraint['end'])

        # Find the optimal place and time to meet
        found_meeting = False
        for location in travel_times.keys():
            travel_time = travel_times['Russian Hill'][location]
            possible_start_time = current_time + timedelta(minutes=travel_time)

            if possible_start_time > meeting_end:  # If it's too late
                break

            if possible_start_time >= meeting_start:  # If we can start meeting in the available window
                if (possible_start_time + duration) <= meeting_end:
                    itinerary.append({
                        "action": "meet",
                        "location": location,
                        "person": constraint['name'],
                        "start_time": possible_start_time.strftime('%H:%M'),
                        "end_time": (possible_start_time + duration).strftime('%H:%M')
                    })
                    found_meeting = True
                    current_time = possible_start_time + duration + timedelta(minutes=travel_times[location]['Russian Hill'])  # Time to go back
                    break

        if not found_meeting:
            return None  # If we can't fit the meeting
    
    return {"itinerary": itinerary}

# Create the schedule
optimal_schedule = calculate_schedule()

# Output result in JSON format
print(json.dumps(optimal_schedule, indent=2))