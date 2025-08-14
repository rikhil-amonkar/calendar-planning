import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define friends with their constraints
    friends = [
        {
            'name': 'Emily',
            'location': 'Richmond District',
            'available_start': 19 * 60,  # 7:00 PM
            'available_end': 21 * 60,    # 9:00 PM
            'required_duration': 15
        },
        {
            'name': 'Margaret',
            'location': 'Financial District',
            'available_start': 16 * 60 + 30,  # 4:30 PM
            'available_end': 20 * 60 + 15,    # 8:15 PM
            'required_duration': 75
        },
        {
            'name': 'Ronald',
            'location': 'North Beach',
            'available_start': 18 * 60 + 30,  # 6:30 PM
            'available_end': 19 * 60 + 30,    # 7:30 PM
            'required_duration': 45
        },
        {
            'name': 'Deborah',
            'location': 'The Castro',
            'available_start': 13 * 60 + 45,  # 1:45 PM
            'available_end': 21 * 60 + 15,    # 9:15 PM
            'required_duration': 90
        },
        {
            'name': 'Jeffrey',
            'location': 'Golden Gate Park',
            'available_start': 11 * 60 + 15,  # 11:15 AM
            'available_end': 14 * 60 + 30,    # 2:30 PM
            'required_duration': 120
        }
    ]

    # Define travel times between locations
    travel_times = {
        'Nob Hill': {
            'Richmond District': 14,
            'Financial District': 9,
            'North Beach': 8,
            'The Castro': 17,
            'Golden Gate Park': 17
        },
        'Richmond District': {
            'Nob Hill': 17,
            'Financial District': 22,
            'North Beach': 17,
            'The Castro': 16,
            'Golden Gate Park': 9
        },
        'Financial District': {
            'Nob Hill': 8,
            'Richmond District': 21,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'North Beach': {
            'Nob Hill': 7,
            'Richmond District': 18,
            'Financial District': 8,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Nob Hill': 16,
            'Richmond District': 16,
            'Financial District': 20,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Richmond District': 7,
            'Financial District': 26,
            'North Beach': 24,
            'The Castro': 13
        }
    }

    best_itinerary = []
    best_count = 0

    # Generate all permutations of friends
    for perm in itertools.permutations(friends):
        current_itinerary = []
        current_location = 'Nob Hill'
        current_time = 540  # 9:00 AM in minutes
        valid = True

        for friend in perm:
            friend_location = friend['location']
            available_start = friend['available_start']
            available_end = friend['available_end']
            duration = friend['required_duration']

            # Calculate travel time
            travel_time = travel_times[current_location][friend_location]
            arrival_time = current_time + travel_time

            # Determine possible start time
            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - duration

            if earliest_start > latest_start:
                valid = False
                break

            # Schedule the meeting
            meeting_start = earliest_start
            meeting_end = meeting_start + duration

            # Add to itinerary
            current_itinerary.append({
                'action': 'meet',
                'location': friend_location,
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })

            # Update current time and location
            current_time = meeting_end
            current_location = friend_location

        if valid and len(current_itinerary) > best_count:
            best_count = len(current_itinerary)
            best_itinerary = current_itinerary

    # Output the best itinerary as JSON
    result = {
        "itinerary": best_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()