import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def is_valid_permutation(perm, travel_times):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Bayview'
    itinerary = []
    for friend in perm:
        # Get travel time from current location to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Determine meeting start time
        meeting_start = max(arrival_time, friend['available_start'])
        # Check if meeting can fit in the friend's available time
        if meeting_start + friend['required_duration'] > friend['available_end']:
            return False, None
        # Record the meeting
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_start + friend['required_duration'])
        })
        # Update current time and location
        current_time = meeting_start + friend['required_duration']
        current_location = friend['location']
    return True, itinerary

def main():
    # Define friends with their constraints
    friends = [
        {
            'name': 'Mary',
            'location': 'Pacific Heights',
            'available_start': 10 * 60,  # 10:00 AM
            'available_end': 19 * 60,    # 7:00 PM
            'required_duration': 45
        },
        {
            'name': 'Lisa',
            'location': 'Mission District',
            'available_start': 20 * 60 + 30,  # 8:30 PM
            'available_end': 22 * 60,         # 10:00 PM
            'required_duration': 75
        },
        {
            'name': 'Betty',
            'location': 'Haight-Ashbury',
            'available_start': 7 * 60 + 15,   # 7:15 AM
            'available_end': 17 * 60 + 15,    # 5:15 PM
            'required_duration': 90
        },
        {
            'name': 'Charles',
            'location': 'Financial District',
            'available_start': 11 * 60 + 15,  # 11:15 AM
            'available_end': 15 * 60,         # 3:00 PM
            'required_duration': 120
        }
    ]
    
    # Define travel times between locations
    travel_times = {
        'Bayview': {
            'Pacific Heights': 23,
            'Mission District': 13,
            'Haight-Ashbury': 19,
            'Financial District': 19
        },
        'Pacific Heights': {
            'Bayview': 22,
            'Mission District': 15,
            'Haight-Ashbury': 11,
            'Financial District': 13
        },
        'Mission District': {
            'Bayview': 15,
            'Pacific Heights': 16,
            'Haight-Ashbury': 12,
            'Financial District': 17
        },
        'Haight-Ashbury': {
            'Bayview': 18,
            'Pacific Heights': 12,
            'Mission District': 11,
            'Financial District': 21
        },
        'Financial District': {
            'Bayview': 19,
            'Pacific Heights': 13,
            'Mission District': 17,
            'Haight-Ashbury': 19
        }
    }
    
    # Find the best permutation
    best_itinerary = None
    # Check permutations from largest to smallest
    for r in range(len(friends), 0, -1):
        for combo in itertools.combinations(friends, r):
            for perm in itertools.permutations(combo):
                is_valid, itinerary = is_valid_permutation(perm, travel_times)
                if is_valid:
                    best_itinerary = itinerary
                    print(json.dumps({"itinerary": best_itinerary}))
                    return
    
    # If no valid permutations found (unlikely in this case)
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()