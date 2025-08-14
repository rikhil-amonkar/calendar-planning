import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_feasible(perm, travel_time, start_location='Marina District', start_time=9*60):
    current_time = start_time
    current_location = start_location
    for meeting in perm:
        # Compute travel time
        travel = travel_time[current_location][meeting['location']]
        arrival_time = current_time + travel
        # Check meeting constraints
        available_start = meeting['available_start']
        available_end = meeting['available_end']
        duration = meeting['required_duration']
        latest_start = available_end - duration
        earliest_start = max(arrival_time, available_start)
        if earliest_start > latest_start:
            return False
        # Update current time and location
        current_time = earliest_start + duration
        current_location = meeting['location']
    return True

def main():
    # Define travel times
    travel_time = {
        'Marina District': {
            'Richmond District': 11,
            'Union Square': 16,
            'Nob Hill': 12,
            "Fisherman's Wharf": 10,
            'Golden Gate Park': 18,
            'Embarcadero': 14,
            'Financial District': 17,
            'North Beach': 11,
            'Presidio': 10,
        },
        'Richmond District': {
            'Marina District': 9,
            'Union Square': 21,
            'Nob Hill': 17,
            "Fisherman's Wharf": 18,
            'Golden Gate Park': 9,
            'Embarcadero': 19,
            'Financial District': 22,
            'North Beach': 17,
            'Presidio': 7,
        },
        'Union Square': {
            'Marina District': 18,
            'Richmond District': 20,
            'Nob Hill': 9,
            "Fisherman's Wharf": 15,
            'Golden Gate Park': 22,
            'Embarcadero': 11,
            'Financial District': 9,
            'North Beach': 10,
            'Presidio': 24,
        },
        'Nob Hill': {
            'Marina District': 11,
            'Richmond District': 14,
            'Union Square': 7,
            "Fisherman's Wharf": 10,
            'Golden Gate Park': 17,
            'Embarcadero': 9,
            'Financial District': 9,
            'North Beach': 8,
            'Presidio': 17,
        },
        "Fisherman's Wharf": {
            'Marina District': 9,
            'Richmond District': 18,
            'Union Square': 13,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Embarcadero': 8,
            'Financial District': 11,
            'North Beach': 6,
            'Presidio': 17,
        },
        'Golden Gate Park': {
            'Marina District': 16,
            'Richmond District': 7,
            'Union Square': 22,
            'Nob Hill': 20,
            "Fisherman's Wharf": 24,
            'Embarcadero': 25,
            'Financial District': 26,
            'North Beach': 23,
            'Presidio': 11,
        },
        'Embarcadero': {
            'Marina District': 12,
            'Richmond District': 21,
            'Union Square': 10,
            'Nob Hill': 10,
            "Fisherman's Wharf": 6,
            'Golden Gate Park': 25,
            'Financial District': 5,
            'North Beach': 5,
            'Presidio': 20,
        },
        'Financial District': {
            'Marina District': 15,
            'Richmond District': 21,
            'Union Square': 9,
            'Nob Hill': 8,
            "Fisherman's Wharf": 10,
            'Golden Gate Park': 23,
            'Embarcadero': 4,
            'North Beach': 7,
            'Presidio': 22,
        },
        'North Beach': {
            'Marina District': 9,
            'Richmond District': 18,
            'Union Square': 7,
            'Nob Hill': 7,
            "Fisherman's Wharf": 5,
            'Golden Gate Park': 22,
            'Embarcadero': 6,
            'Financial District': 8,
            'Presidio': 17,
        },
        'Presidio': {
            'Marina District': 11,
            'Richmond District': 7,
            'Union Square': 22,
            'Nob Hill': 18,
            "Fisherman's Wharf": 19,
            'Golden Gate Park': 12,
            'Embarcadero': 20,
            'Financial District': 23,
            'North Beach': 18,
        },
    }

    # Define the meetings
    meetings = [
        {
            'person': 'Stephanie',
            'location': 'Richmond District',
            'available_start': 16 * 60 + 15,  # 4:15 PM
            'available_end': 21 * 60 + 30,    # 9:30 PM
            'required_duration': 75,
        },
        {
            'person': 'William',
            'location': 'Union Square',
            'available_start': 10 * 60 + 45,  # 10:45 AM
            'available_end': 17 * 60 + 30,    # 5:30 PM
            'required_duration': 45,
        },
        {
            'person': 'Elizabeth',
            'location': 'Nob Hill',
            'available_start': 12 * 60 + 15,  # 12:15 PM
            'available_end': 15 * 60 + 0,     # 3:00 PM
            'required_duration': 105,
        },
        {
            'person': 'Joseph',
            'location': "Fisherman's Wharf",
            'available_start': 12 * 60 + 45,  # 12:45 PM
            'available_end': 14 * 60 + 0,     # 2:00 PM
            'required_duration': 75,
        },
        {
            'person': 'Anthony',
            'location': 'Golden Gate Park',
            'available_start': 13 * 60 + 0,   # 1:00 PM
            'available_end': 20 * 60 + 30,    # 8:30 PM
            'required_duration': 75,
        },
        {
            'person': 'Barbara',
            'location': 'Embarcadero',
            'available_start': 19 * 60 + 15,  # 7:15 PM
            'available_end': 20 * 60 + 30,    # 8:30 PM
            'required_duration': 75,
        },
        {
            'person': 'Carol',
            'location': 'Financial District',
            'available_start': 11 * 60 + 45,  # 11:45 AM
            'available_end': 16 * 60 + 15,    # 4:15 PM
            'required_duration': 60,
        },
        {
            'person': 'Sandra',
            'location': 'North Beach',
            'available_start': 10 * 60 + 0,   # 10:00 AM
            'available_end': 12 * 60 + 30,    # 12:30 PM
            'required_duration': 15,
        },
        {
            'person': 'Kenneth',
            'location': 'Presidio',
            'available_start': 21 * 60 + 15,  # 9:15 PM
            'available_end': 22 * 60 + 15,    # 10:15 PM
            'required_duration': 45,
        },
    ]

    # Find the optimal permutation
    for length in range(len(meetings), 0, -1):
        for perm in itertools.permutations(meetings, length):
            if is_feasible(perm, travel_time):
                # Generate the itinerary
                itinerary = []
                current_time = 9 * 60  # Start time
                current_location = 'Marina District'
                for meeting in perm:
                    # Compute travel time
                    travel = travel_time[current_location][meeting['location']]
                    arrival_time = current_time + travel
                    # Compute start and end times
                    available_start = meeting['available_start']
                    available_end = meeting['available_end']
                    duration = meeting['required_duration']
                    latest_start = available_end - duration
                    start_time_minutes = max(arrival_time, available_start)
                    end_time_minutes = start_time_minutes + duration
                    # Append to itinerary
                    itinerary.append({
                        'action': 'meet',
                        'location': meeting['location'],
                        'person': meeting['person'],
                        'start_time': minutes_to_time_str(start_time_minutes),
                        'end_time': minutes_to_time_str(end_time_minutes),
                    })
                    # Update current time and location
                    current_time = end_time_minutes
                    current_location = meeting['location']
                # Output as JSON
                print(json.dumps({"itinerary": itinerary}))
                return

    # If no meetings can be attended
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()