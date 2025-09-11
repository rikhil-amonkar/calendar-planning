import itertools
import json

def main():
    # Define friends data
    friends = [
        {
            'name': 'Joseph',
            'location': "Golden Gate Park",
            'start_time': 510,  # 8:30 AM
            'end_time': 1275,    # 9:15 PM
            'min_duration': 105
        },
        {
            'name': 'Amanda',
            'location': 'Marina District',
            'start_time': 885,   # 2:45 PM
            'end_time': 1170,    # 7:30 PM
            'min_duration': 105
        },
        {
            'name': 'Melissa',
            'location': 'The Castro',
            'start_time': 570,   # 9:30 AM
            'end_time': 1020,    # 5:00 PM
            'min_duration': 30
        },
        {
            'name': 'Jeffrey',
            'location': "Fisherman's Wharf",
            'start_time': 765,   # 12:45 PM
            'end_time': 1125,    # 6:45 PM
            'min_duration': 120
        },
        {
            'name': 'Matthew',
            'location': 'Bayview',
            'start_time': 615,   # 10:15 AM
            'end_time': 795,     # 1:15 PM
            'min_duration': 30
        },
        {
            'name': 'Nancy',
            'location': 'Pacific Heights',
            'start_time': 1020,  # 5:00 PM
            'end_time': 1290,    # 9:30 PM
            'min_duration': 105
        },
        {
            'name': 'Karen',
            'location': 'Mission District',
            'start_time': 1050,  # 5:30 PM
            'end_time': 1230,    # 8:30 PM
            'min_duration': 105
        },
        {
            'name': 'Robert',
            'location': 'Alamo Square',
            'start_time': 675,   # 11:15 AM
            'end_time': 1050,    # 5:30 PM
            'min_duration': 120
        }
    ]

    # Define travel times between locations
    travel_time = {
        'Presidio': {
            'Marina District': 11,
            'The Castro': 21,
            "Fisherman's Wharf": 19,
            'Bayview': 31,
            'Pacific Heights': 11,
            'Mission District': 26,
            'Alamo Square': 19,
            "Golden Gate Park": 12,
        },
        'Marina District': {
            'Presidio': 10,
            'The Castro': 22,
            "Fisherman's Wharf": 10,
            'Bayview': 27,
            'Pacific Heights': 7,
            'Mission District': 20,
            'Alamo Square': 15,
            "Golden Gate Park": 18,
        },
        'The Castro': {
            'Presidio': 20,
            'Marina District': 21,
            "Fisherman's Wharf": 24,
            'Bayview': 19,
            'Pacific Heights': 16,
            'Mission District': 7,
            'Alamo Square': 8,
            "Golden Gate Park": 11,
        },
        "Fisherman's Wharf": {
            'Presidio': 17,
            'Marina District': 9,
            'The Castro': 27,
            'Bayview': 26,
            'Pacific Heights': 12,
            'Mission District': 22,
            'Alamo Square': 21,
            "Golden Gate Park": 25,
        },
        'Bayview': {
            'Presidio': 32,
            'Marina District': 27,
            'The Castro': 19,
            "Fisherman's Wharf": 25,
            'Pacific Heights': 23,
            'Mission District': 13,
            'Alamo Square': 16,
            "Golden Gate Park": 22,
        },
        'Pacific Heights': {
            'Presidio': 11,
            'Marina District': 6,
            'The Castro': 16,
            "Fisherman's Wharf": 13,
            'Bayview': 22,
            'Mission District': 15,
            'Alamo Square': 10,
            "Golden Gate Park": 15,
        },
        'Mission District': {
            'Presidio': 25,
            'Marina District': 19,
            'The Castro': 7,
            "Fisherman's Wharf": 22,
            'Bayview': 14,
            'Pacific Heights': 16,
            'Alamo Square': 11,
            "Golden Gate Park": 17,
        },
        'Alamo Square': {
            'Presidio': 17,
            'Marina District': 15,
            'The Castro': 8,
            "Fisherman's Wharf": 19,
            'Bayview': 16,
            'Pacific Heights': 10,
            'Mission District': 10,
            "Golden Gate Park": 9,
        },
        "Golden Gate Park": {
            'Presidio': 11,
            'Marina District': 16,
            'The Castro': 13,
            "Fisherman's Wharf": 24,
            'Bayview': 23,
            'Pacific Heights': 16,
            'Mission District': 17,
            'Alamo Square': 9,
        },
    }

    # Check permutations in order of largest to smallest
    for k in range(len(friends), 0, -1):
        for combo in itertools.combinations(friends, k):
            for perm in itertools.permutations(combo):
                # Check if this permutation is feasible
                current_time = 540  # 9:00 AM
                current_location = 'Presidio'
                valid = True
                itinerary = []
                for friend in perm:
                    loc = friend['location']
                    start = friend['start_time']
                    end = friend['end_time']
                    duration = friend['min_duration']
                    # Calculate arrival time at this location
                    travel_duration = travel_time[current_location][loc]
                    arrival_time = current_time + travel_duration
                    # Determine meeting start time
                    meeting_start = max(arrival_time, start)
                    # Check if meeting can be scheduled
                    if meeting_start + duration > end:
                        valid = False
                        break
                    # Record the meeting
                    itinerary.append({
                        'action': 'meet',
                        'location': loc,
                        'person': friend['name'],
                        'start_time': time_to_str(meeting_start),
                        'end_time': time_to_str(meeting_start + duration)
                    })
                    # Update current time and location
                    current_time = meeting_start + duration
                    current_location = loc
                if valid:
                    # Found a valid itinerary
                    output = {'itinerary': itinerary}
                    print(json.dumps(output, indent=2))
                    return

def time_to_str(minutes):
    """Convert minutes since midnight to H:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()