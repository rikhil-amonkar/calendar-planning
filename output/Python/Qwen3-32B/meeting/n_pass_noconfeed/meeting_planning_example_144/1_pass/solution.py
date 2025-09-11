import itertools
import json

def mins_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define travel times between locations (in minutes)
    travel_time = {
        ('Castro', 'Mission District'): 7,
        ('Castro', 'Financial District'): 20,
        ('Mission District', 'Castro'): 7,
        ('Mission District', 'Financial District'): 17,
        ('Financial District', 'Castro'): 23,
        ('Financial District', 'Mission District'): 17,
    }

    # Define friends' constraints
    friends = [
        {
            'name': 'Laura',
            'location': 'Mission District',
            'available_start': 735,  # 12:15 PM
            'available_end': 1185,   # 7:45 PM
            'required_duration': 75
        },
        {
            'name': 'Anthony',
            'location': 'Financial District',
            'available_start': 750,  # 12:30 PM
            'available_end': 885,    # 2:45 PM
            'required_duration': 30
        }
    ]

    # Starting conditions
    start_location = 'Castro'
    start_time = 540  # 9:00 AM in minutes since midnight

    # Check all permutations of friends
    for permutation in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        valid = True

        for friend in permutation:
            # Calculate travel time to friend's location
            travel_key = (current_location, friend['location'])
            if travel_key not in travel_time:
                valid = False
                break
            travel_duration = travel_time[travel_key]
            current_time += travel_duration

            # Calculate earliest possible start time for the meeting
            earliest_start = max(current_time, friend['available_start'])
            latest_start = friend['available_end'] - friend['required_duration']

            if earliest_start > latest_start:
                valid = False
                break

            # Schedule the meeting
            meeting_end = earliest_start + friend['required_duration']
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': mins_to_time(earliest_start),
                'end_time': mins_to_time(meeting_end)
            })

            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']

        if valid:
            # Return the first valid itinerary found
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return

    # If no valid itinerary is found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()