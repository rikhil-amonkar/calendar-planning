import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_feasible(perm, travel_times):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Union Square'
    for friend in perm:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        required_duration = friend['required_duration']
        # Start meeting is max of arrival and available start
        start_meeting = max(arrival_time, available_start)
        end_meeting = start_meeting + required_duration
        if end_meeting > available_end:
            return False
        current_time = end_meeting
        current_location = friend['location']
    return True

def generate_itinerary(perm, travel_times):
    current_time = 9 * 60  # 9:00 AM
    current_location = 'Union Square'
    itinerary = []
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        required_duration = friend['required_duration']
        start_meeting = max(arrival_time, available_start)
        end_meeting = start_meeting + required_duration
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(start_meeting),
            'end_time': minutes_to_time_str(end_meeting)
        })
        current_time = end_meeting
        current_location = friend['location']
    return itinerary

def main():
    # Define friends
    friends = [
        {
            'name': 'Kimberly',
            'location': 'North Beach',
            'available_start': 7 * 60,
            'available_end': 10 * 60 + 30,
            'required_duration': 15
        },
        {
            'name': 'Brian',
            'location': "Fisherman's Wharf",
            'available_start': 9 * 60 + 30,
            'available_end': 15 * 60 + 30,
            'required_duration': 45
        },
        {
            'name': 'Kenneth',
            'location': 'Nob Hill',
            'available_start': 12 * 60 + 15,
            'available_end': 17 * 60 + 15,
            'required_duration': 105
        },
        {
            'name': 'Joseph',
            'location': 'Embarcadero',
            'available_start': 15 * 60 + 30,
            'available_end': 19 * 60 + 30,
            'required_duration': 75
        },
        {
            'name': 'Joshua',
            'location': 'Presidio',
            'available_start': 16 * 60 + 30,
            'available_end': 18 * 60 + 15,
            'required_duration': 105
        },
        {
            'name': 'Betty',
            'location': 'Haight-Ashbury',
            'available_start': 19 * 60,
            'available_end': 20 * 60 + 30,
            'required_duration': 90
        },
        {
            'name': 'Steven',
            'location': 'Mission District',
            'available_start': 19 * 60 + 30,
            'available_end': 21 * 60,
            'required_duration': 90
        },
        {
            'name': 'Melissa',
            'location': 'The Castro',
            'available_start': 20 * 60 + 15,
            'available_end': 21 * 60 + 15,
            'required_duration': 30
        },
        {
            'name': 'Barbara',
            'location': 'Alamo Square',
            'available_start': 20 * 60 + 45,
            'available_end': 21 * 60 + 45,
            'required_duration': 15
        }
    ]

    # Define travel times
    travel_times = {
        'Union Square': {
            'The Castro': 17,
            'North Beach': 10,
            'Embarcadero': 11,
            'Alamo Square': 15,
            'Nob Hill': 9,
            'Presidio': 24,
            "Fisherman's Wharf": 15,
            'Mission District': 14,
            'Haight-Ashbury': 18
        },
        'The Castro': {
            'Union Square': 19,
            'North Beach': 20,
            'Embarcadero': 22,
            'Alamo Square': 8,
            'Nob Hill': 16,
            'Presidio': 20,
            "Fisherman's Wharf": 24,
            'Mission District': 7,
            'Haight-Ashbury': 6
        },
        'North Beach': {
            'Union Square': 7,
            'The Castro': 23,
            'Embarcadero': 6,
            'Alamo Square': 16,
            'Nob Hill': 7,
            'Presidio': 17,
            "Fisherman's Wharf": 5,
            'Mission District': 18,
            'Haight-Ashbury': 18
        },
        'Embarcadero': {
            'Union Square': 10,
            'The Castro': 25,
            'North Beach': 5,
            'Alamo Square': 19,
            'Nob Hill': 10,
            'Presidio': 20,
            "Fisherman's Wharf": 6,
            'Mission District': 20,
            'Haight-Ashbury': 21
        },
        'Alamo Square': {
            'Union Square': 14,
            'The Castro': 8,
            'North Beach': 15,
            'Embarcadero': 16,
            'Nob Hill': 11,
            'Presidio': 17,
            "Fisherman's Wharf": 19,
            'Mission District': 10,
            'Haight-Ashbury': 5
        },
        'Nob Hill': {
            'Union Square': 7,
            'The Castro': 17,
            'North Beach': 8,
            'Embarcadero': 9,
            'Alamo Square': 11,
            'Presidio': 17,
            "Fisherman's Wharf": 10,
            'Mission District': 13,
            'Haight-Ashbury': 13
        },
        'Presidio': {
            'Union Square': 22,
            'The Castro': 21,
            'North Beach': 18,
            'Embarcadero': 20,
            'Alamo Square': 19,
            'Nob Hill': 18,
            "Fisherman's Wharf": 19,
            'Mission District': 26,
            'Haight-Ashbury': 15
        },
        "Fisherman's Wharf": {
            'Union Square': 13,
            'The Castro': 27,
            'North Beach': 6,
            'Embarcadero': 8,
            'Alamo Square': 21,
            'Nob Hill': 11,
            'Presidio': 17,
            'Mission District': 22,
            'Haight-Ashbury': 22
        },
        'Mission District': {
            'Union Square': 15,
            'The Castro': 7,
            'North Beach': 17,
            'Embarcadero': 19,
            'Alamo Square': 11,
            'Nob Hill': 12,
            'Presidio': 25,
            "Fisherman's Wharf": 22,
            'Haight-Ashbury': 12
        },
        'Haight-Ashbury': {
            'Union Square': 19,
            'The Castro': 6,
            'North Beach': 19,
            'Embarcadero': 20,
            'Alamo Square': 5,
            'Nob Hill': 15,
            'Presidio': 15,
            "Fisherman's Wharf": 23,
            'Mission District': 11
        }
    }

    best_itinerary = None
    # Check permutations in descending order of length
    for length in range(len(friends), 0, -1):
        for perm in itertools.permutations(friends, length):
            if is_feasible(perm, travel_times):
                best_itinerary = generate_itinerary(perm, travel_times)
                # Output the JSON and exit
                print(json.dumps({"itinerary": best_itinerary}, indent=2))
                return

    # If no friends can be met
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()