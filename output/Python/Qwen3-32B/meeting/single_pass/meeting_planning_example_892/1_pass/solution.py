import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def simulate(perm, travel_time, friends_info):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Marina District'
    itinerary = []
    for friend in perm:
        loc = friend['location']
        available_start = friend['available_start']
        available_end = friend['available_end']
        duration = friend['required_duration']
        # Travel time
        travel = travel_time[current_location][loc]
        arrival_time = current_time + travel
        # Determine meeting start time
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        if meeting_end <= available_end:
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': loc,
                'person': friend['name'],
                'start_time': format_time(meeting_start),
                'end_time': format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = loc
        else:
            # Can't meet this friend, break
            break
    return itinerary

def main():
    # Define friends with their details
    friends = [
        {
            'name': 'Laura',
            'location': 'Embarcadero',
            'available_start': 7 * 60 + 45,  # 7:45 AM
            'available_end': 13 * 60 + 15,   # 1:15 PM
            'required_duration': 105
        },
        {
            'name': 'Charles',
            'location': 'Bayview',
            'available_start': 11 * 60 + 30,  # 11:30 AM
            'available_end': 14 * 60 + 30,   # 2:30 PM
            'required_duration': 45
        },
        {
            'name': 'Robert',
            'location': 'Sunset District',
            'available_start': 16 * 60 + 45,  # 4:45 PM
            'available_end': 21 * 60 + 0,   # 9:00 PM
            'required_duration': 30
        },
        {
            'name': 'Karen',
            'location': 'Richmond District',
            'available_start': 19 * 60 + 15,  # 7:15 PM
            'available_end': 21 * 60 + 30,   # 9:30 PM
            'required_duration': 60
        },
        {
            'name': 'Rebecca',
            'location': 'Nob Hill',
            'available_start': 16 * 60 + 15,  # 4:15 PM
            'available_end': 20 * 60 + 30,   # 8:30 PM
            'required_duration': 90
        },
        {
            'name': 'Margaret',
            'location': 'Chinatown',
            'available_start': 14 * 60 + 15,  # 2:15 PM
            'available_end': 19 * 60 + 45,   # 7:45 PM
            'required_duration': 120
        },
        {
            'name': 'Patricia',
            'location': 'Haight-Ashbury',
            'available_start': 14 * 60 + 30,  # 2:30 PM
            'available_end': 20 * 60 + 30,   # 8:30 PM
            'required_duration': 45
        },
        {
            'name': 'Mark',
            'location': 'North Beach',
            'available_start': 14 * 60 + 0,  # 2:00 PM
            'available_end': 18 * 60 + 30,   # 6:30 PM
            'required_duration': 105
        },
        {
            'name': 'Melissa',
            'location': 'Russian Hill',
            'available_start': 13 * 60 + 0,  # 1:00 PM
            'available_end': 19 * 60 + 45,   # 7:45 PM
            'required_duration': 30
        }
    ]

    # Define travel times as a dictionary of dictionaries
    travel_time = {
        'Marina District': {
            'Bayview': 27,
            'Sunset District': 19,
            'Richmond District': 11,
            'Nob Hill': 12,
            'Chinatown': 15,
            'Haight-Ashbury': 16,
            'North Beach': 11,
            'Russian Hill': 8,
            'Embarcadero': 14
        },
        'Bayview': {
            'Marina District': 27,
            'Sunset District': 23,
            'Richmond District': 25,
            'Nob Hill': 20,
            'Chinatown': 19,
            'Haight-Ashbury': 19,
            'North Beach': 22,
            'Russian Hill': 23,
            'Embarcadero': 19
        },
        'Sunset District': {
            'Marina District': 21,
            'Bayview': 22,
            'Richmond District': 12,
            'Nob Hill': 27,
            'Chinatown': 30,
            'Haight-Ashbury': 15,
            'North Beach': 28,
            'Russian Hill': 24,
            'Embarcadero': 30
        },
        'Richmond District': {
            'Marina District': 9,
            'Bayview': 27,
            'Sunset District': 11,
            'Nob Hill': 17,
            'Chinatown': 20,
            'Haight-Ashbury': 10,
            'North Beach': 17,
            'Russian Hill': 13,
            'Embarcadero': 19
        },
        'Nob Hill': {
            'Marina District': 11,
            'Bayview': 19,
            'Sunset District': 24,
            'Richmond District': 14,
            'Chinatown': 6,
            'Haight-Ashbury': 13,
            'North Beach': 8,
            'Russian Hill': 5,
            'Embarcadero': 9
        },
        'Chinatown': {
            'Marina District': 12,
            'Bayview': 20,
            'Sunset District': 29,
            'Richmond District': 20,
            'Nob Hill': 9,
            'Haight-Ashbury': 19,
            'North Beach': 3,
            'Russian Hill': 7,
            'Embarcadero': 5
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Bayview': 18,
            'Sunset District': 15,
            'Richmond District': 10,
            'Nob Hill': 15,
            'Chinatown': 19,
            'North Beach': 19,
            'Russian Hill': 17,
            'Embarcadero': 20
        },
        'North Beach': {
            'Marina District': 9,
            'Bayview': 25,
            'Sunset District': 27,
            'Richmond District': 18,
            'Nob Hill': 7,
            'Chinatown': 6,
            'Haight-Ashbury': 18,
            'Russian Hill': 4,
            'Embarcadero': 6
        },
        'Russian Hill': {
            'Marina District': 7,
            'Bayview': 23,
            'Sunset District': 23,
            'Richmond District': 14,
            'Nob Hill': 5,
            'Chinatown': 9,
            'North Beach': 5,
            'Embarcadero': 8
        },
        'Embarcadero': {
            'Marina District': 12,
            'Bayview': 21,
            'Sunset District': 30,
            'Richmond District': 21,
            'Nob Hill': 10,
            'Chinatown': 7,
            'Haight-Ashbury': 21,
            'North Beach': 5,
            'Russian Hill': 8
        }
    }

    best_itinerary = []
    for perm in itertools.permutations(friends):
        itinerary = simulate(perm, travel_time, friends)
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary
    print(json.dumps({"itinerary": best_itinerary}))

if __name__ == "__main__":
    main()