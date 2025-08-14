import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times between locations
    travel_times = {
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            "Fisherman's Wharf": 24,
            'The Castro': 13,
            'Chinatown': 23,
            'Alamo Square': 10,
            'North Beach': 24,
            'Russian Hill': 19
        },
        'Haight-Ashbury': {
            'Golden Gate Park': 7,
            "Fisherman's Wharf": 23,
            'The Castro': 6,
            'Chinatown': 19,
            'Alamo Square': 5,
            'North Beach': 19,
            'Russian Hill': 17
        },
        "Fisherman's Wharf": {
            'Golden Gate Park': 25,
            'Haight-Ashbury': 22,
            'The Castro': 26,
            'Chinatown': 12,
            'Alamo Square': 20,
            'North Beach': 6,
            'Russian Hill': 7
        },
        'The Castro': {
            'Golden Gate Park': 11,
            'Haight-Ashbury': 6,
            "Fisherman's Wharf": 24,
            'Chinatown': 20,
            'Alamo Square': 8,
            'North Beach': 20,
            'Russian Hill': 18
        },
        'Chinatown': {
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            "Fisherman's Wharf": 8,
            'The Castro': 22,
            'Alamo Square': 17,
            'North Beach': 3,
            'Russian Hill': 7
        },
        'Alamo Square': {
            'Golden Gate Park': 9,
            'Haight-Ashbury': 5,
            "Fisherman's Wharf": 19,
            'The Castro': 8,
            'Chinatown': 16,
            'North Beach': 15,
            'Russian Hill': 13
        },
        'North Beach': {
            'Golden Gate Park': 22,
            'Haight-Ashbury': 18,
            "Fisherman's Wharf": 5,
            'The Castro': 22,
            'Chinatown': 6,
            'Alamo Square': 16,
            'Russian Hill': 4
        },
        'Russian Hill': {
            'Golden Gate Park': 21,
            'Haight-Ashbury': 17,
            "Fisherman's Wharf": 7,
            'The Castro': 21,
            'Chinatown': 9,
            'Alamo Square': 15,
            'North Beach': 5
        }
    }

    # Define friends' constraints
    friends = [
        {
            'name': 'Carol',
            'location': "Haight-Ashbury",
            'start_time': 21 * 60 + 30,  # 9:30 PM
            'end_time': 22 * 60 + 30,    # 10:30 PM
            'required_duration': 60
        },
        {
            'name': 'Laura',
            'location': "Fisherman's Wharf",
            'start_time': 11 * 60 + 45,  # 11:45 AM
            'end_time': 21 * 60 + 30,    # 9:30 PM
            'required_duration': 60
        },
        {
            'name': 'Karen',
            'location': "The Castro",
            'start_time': 7 * 60 + 15,   # 7:15 AM
            'end_time': 14 * 60,         # 2:00 PM
            'required_duration': 75
        },
        {
            'name': 'Elizabeth',
            'location': "Chinatown",
            'start_time': 12 * 60 + 15,  # 12:15 PM
            'end_time': 21 * 60 + 30,    # 9:30 PM
            'required_duration': 75
        },
        {
            'name': 'Deborah',
            'location': "Alamo Square",
            'start_time': 12 * 60,       # 12:00 PM
            'end_time': 15 * 60,         # 3:00 PM
            'required_duration': 105
        },
        {
            'name': 'Jason',
            'location': "North Beach",
            'start_time': 14 * 60 + 45,  # 2:45 PM
            'end_time': 19 * 60,         # 7:00 PM
            'required_duration': 90
        },
        {
            'name': 'Steven',
            'location': "Russian Hill",
            'start_time': 14 * 60 + 45,  # 2:45 PM
            'end_time': 18 * 60 + 30,    # 6:30 PM
            'required_duration': 120
        }
    ]

    best_itinerary = []

    def backtrack(current_time, current_location, visited_indices, itinerary):
        nonlocal best_itinerary

        # Update best itinerary if this one is better
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary.copy()

        # Try all friends not yet visited
        for i in range(len(friends)):
            if i not in visited_indices:
                friend = friends[i]
                # Compute arrival time at friend's location
                travel_time = travel_times[current_location][friend['location']]
                arrival_time = current_time + travel_time

                # Determine earliest possible start time for the meeting
                earliest_start = max(arrival_time, friend['start_time'])

                # Check if meeting can fit into friend's schedule
                required = friend['required_duration']
                if earliest_start + required <= friend['end_time']:
                    # Create new state for recursion
                    new_visited = visited_indices.copy()
                    new_visited.add(i)
                    new_itinerary = itinerary.copy()
                    new_itinerary.append({
                        'action': 'meet',
                        'location': friend['location'],
                        'person': friend['name'],
                        'start_time': earliest_start,
                        'end_time': earliest_start + required
                    })
                    # Recurse
                    backtrack(
                        earliest_start + required,
                        friend['location'],
                        new_visited,
                        new_itinerary
                    )

    # Initial call: starting at 9:00 AM (540) at Golden Gate Park
    initial_time = 9 * 60  # 540 minutes
    initial_location = 'Golden Gate Park'
    backtrack(initial_time, initial_location, set(), [])

    # Convert best itinerary times to strings
    for entry in best_itinerary:
        entry['start_time'] = to_time_str(entry['start_time'])
        entry['end_time'] = to_time_str(entry['end_time'])

    # Output as JSON
    result = {
        "itinerary": best_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()