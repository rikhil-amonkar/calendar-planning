import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define friends with their constraints
    friends = [
        {
            'name': 'Karen',
            'location': 'Mission District',
            'start': 14*60 + 15,  # 855
            'end': 22*60,  # 1320
            'duration': 30
        },
        {
            'name': 'Richard',
            'location': "Fisherman's Wharf",
            'start': 14*60 +30, # 870
            'end': 17*60 +30, # 1050
            'duration': 30
        },
        {
            'name': 'Robert',
            'location': 'Presidio',
            'start': 21*60 +45, # 1305
            'end': 22*60 +45, # 1365
            'duration': 60
        },
        {
            'name': 'Joseph',
            'location': 'Union Square',
            'start': 11*60 +45, # 705
            'end': 14*60 +45, # 865
            'duration': 120
        },
        {
            'name': 'Helen',
            'location': 'Sunset District',
            'start': 14*60 +45, # 885
            'end': 20*60 +45, # 1245
            'duration': 105
        },
        {
            'name': 'Elizabeth',
            'location': 'Financial District',
            'start': 10*60, # 600
            'end': 12*60 +45, # 765
            'duration': 75
        },
        {
            'name': 'Kimberly',
            'location': 'Haight-Ashbury',
            'start': 14*60 +15, # 855
            'end': 17*60 +30, # 1050
            'duration': 105
        },
        {
            'name': 'Ashley',
            'location': 'Russian Hill',
            'start': 11*60 +30, # 690
            'end': 21*60 +30, # 1290
            'duration': 45
        }
    ]

    # Define travel times between locations
    travel_times = {
        'Marina District': {
            'Mission District': 20,
            "Fisherman's Wharf": 10,
            'Presidio': 10,
            'Union Square': 16,
            'Sunset District': 19,
            'Financial District': 17,
            'Haight-Ashbury': 16,
            'Russian Hill': 8,
        },
        'Mission District': {
            'Marina District': 19,
            "Fisherman's Wharf": 22,
            'Presidio': 25,
            'Union Square': 15,
            'Sunset District': 24,
            'Financial District': 15,
            'Haight-Ashbury': 12,
            'Russian Hill': 15,
        },
        "Fisherman's Wharf": {
            'Marina District': 9,
            'Mission District': 22,
            'Presidio': 17,
            'Union Square': 13,
            'Sunset District': 27,
            'Financial District': 11,
            'Haight-Ashbury': 22,
            'Russian Hill': 7,
        },
        'Presidio': {
            'Marina District': 11,
            'Mission District': 26,
            "Fisherman's Wharf": 19,
            'Union Square': 22,
            'Sunset District': 15,
            'Financial District': 23,
            'Haight-Ashbury': 15,
            'Russian Hill': 14,
        },
        'Union Square': {
            'Marina District': 18,
            'Mission District': 14,
            "Fisherman's Wharf": 15,
            'Presidio': 24,
            'Sunset District': 27,
            'Financial District': 9,
            'Haight-Ashbury': 18,
            'Russian Hill': 13,
        },
        'Sunset District': {
            'Marina District': 21,
            'Mission District': 25,
            "Fisherman's Wharf": 29,
            'Presidio': 16,
            'Union Square': 30,
            'Financial District': 30,
            'Haight-Ashbury': 15,
            'Russian Hill': 24,
        },
        'Financial District': {
            'Marina District': 15,
            'Mission District': 15,
            "Fisherman's Wharf": 10,
            'Presidio': 22,
            'Union Square': 9,
            'Sunset District': 30,
            'Haight-Ashbury': 19,
            'Russian Hill': 11,
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Mission District': 11,
            "Fisherman's Wharf": 23,
            'Presidio': 15,
            'Union Square': 19,
            'Sunset District': 15,
            'Financial District': 21,
            'Russian Hill': 17,
        },
        'Russian Hill': {
            'Marina District': 7,
            'Mission District': 16,
            "Fisherman's Wharf": 7,
            'Presidio': 14,
            'Union Square': 10,
            'Sunset District': 23,
            'Financial District': 11,
            'Haight-Ashbury': 17,
        },
    }

    # Start time at Marina District: 9:00 AM = 540 minutes
    start_time = 540  # minutes since midnight
    start_location = 'Marina District'

    # Check all possible permutations of friends, starting with largest subsets
    for k in range(len(friends), 0, -1):
        for combo in itertools.combinations(friends, k):
            for perm in itertools.permutations(combo):
                # Check if this permutation is valid
                current_time = start_time
                current_location = start_location
                valid = True
                for friend in perm:
                    # Get travel time from current location to friend's location
                    dest = friend['location']
                    if current_location not in travel_times or dest not in travel_times[current_location]:
                        valid = False
                        break
                    travel_time = travel_times[current_location][dest]
                    arrival_time = current_time + travel_time
                    friend_start = friend['start']
                    friend_end = friend['end']
                    required = friend['duration']
                    # Earliest possible start is max(arrival_time, friend's start time)
                    start = max(arrival_time, friend_start)
                    # Check if there's enough time for the meeting
                    if start + required > friend_end:
                        valid = False
                        break
                    # Update current time and location
                    current_time = start + required
                    current_location = dest
                if valid:
                    # Found a valid permutation; now build the itinerary
                    itinerary = []
                    current_time = start_time
                    current_location = start_location
                    for friend in perm:
                        dest = friend['location']
                        travel_time = travel_times[current_location][dest]
                        arrival_time = current_time + travel_time
                        friend_start = friend['start']
                        friend_end = friend['end']
                        required = friend['duration']
                        start = max(arrival_time, friend_start)
                        end = start + required
                        # Convert to time strings
                        start_str = minutes_to_time_str(start)
                        end_str = minutes_to_time_str(end)
                        itinerary.append({
                            "action": "meet",
                            "location": dest,
                            "person": friend['name'],
                            "start_time": start_str,
                            "end_time": end_str
                        })
                        current_time = end
                        current_location = dest
                    # Output as JSON
                    result = {"itinerary": itinerary}
                    print(json.dumps(result, indent=2))
                    return

    # If no valid permutations found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()