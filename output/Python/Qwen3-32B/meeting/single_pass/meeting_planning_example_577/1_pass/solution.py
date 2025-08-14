import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_best(current_time, current_location, met_indices, current_itinerary, friends, travel_times):
    best_itinerary = list(current_itinerary)
    
    for i in range(len(friends)):
        if i not in met_indices:
            friend = friends[i]
            dest = friend['location']
            required_duration = friend['required_duration']
            available_start = friend['available_start']
            available_end = friend['available_end']
            
            # Get travel time
            try:
                travel_time = travel_times[current_location][dest]
            except KeyError:
                # If no travel time defined (shouldn't happen here)
                continue
            
            arrival_time = current_time + travel_time
            if arrival_time > available_end:
                continue  # Can't meet this friend
            
            meeting_end = arrival_time + required_duration
            if meeting_end > available_end:
                continue  # Not enough time for the meeting
            
            # Create new itinerary entry
            start_time = minutes_to_time(arrival_time)
            end_time = minutes_to_time(meeting_end)
            
            new_itinerary = list(current_itinerary)
            new_itinerary.append({
                'action': 'meet',
                'location': dest,
                'person': friend['name'],
                'start_time': start_time,
                'end_time': end_time
            })
            
            # Recursively find best from this new state
            new_met = met_indices | {i}
            recursive_result = find_best(
                meeting_end, dest, new_met, new_itinerary, friends, travel_times
            )
            
            if len(recursive_result) > len(best_itinerary):
                best_itinerary = recursive_result
    
    return best_itinerary

def main():
    # Define friends
    friends = [
        {
            'name': 'Anthony',
            'location': 'Alamo Square',
            'available_start': 7 * 60 + 45,  # 7:45 AM
            'available_end': 19 * 60 + 45,    # 7:45 PM
            'required_duration': 15
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'available_start': 8 * 60 + 30,   # 8:30 AM
            'available_end': 17 * 60,         # 5:00 PM
            'required_duration': 75
        },
        {
            'name': 'Sandra',
            'location': 'Pacific Heights',
            'available_start': 14 * 60 + 45,  # 2:45 PM
            'available_end': 21 * 60 + 45,    # 9:45 PM
            'required_duration': 45
        },
        {
            'name': 'Kevin',
            'location': "Fisherman's Wharf",
            'available_start': 19 * 60 + 15,  # 7:15 PM
            'available_end': 21 * 60 + 45,    # 9:45 PM
            'required_duration': 75
        },
        {
            'name': 'Stephanie',
            'location': 'Russian Hill',
            'available_start': 20 * 60,       # 8:00 PM
            'available_end': 20 * 60 + 45,    # 8:45 PM
            'required_duration': 15
        }
    ]
    
    # Define travel times between locations
    travel_times = {
        'Haight-Ashbury': {
            'Russian Hill': 17,
            "Fisherman's Wharf": 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Alamo Square': 5,
            'Pacific Heights': 12
        },
        'Russian Hill': {
            'Haight-Ashbury': 17,
            "Fisherman's Wharf": 7,
            'Nob Hill': 5,
            'Golden Gate Park': 21,
            'Alamo Square': 15,
            'Pacific Heights': 7
        },
        "Fisherman's Wharf": {
            'Haight-Ashbury': 22,
            'Russian Hill': 7,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Alamo Square': 20,
            'Pacific Heights': 12
        },
        'Nob Hill': {
            'Haight-Ashbury': 13,
            'Russian Hill': 5,
            "Fisherman's Wharf": 11,
            'Golden Gate Park': 17,
            'Alamo Square': 11,
            'Pacific Heights': 8
        },
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            'Russian Hill': 19,
            "Fisherman's Wharf": 24,
            'Nob Hill': 17,
            'Alamo Square': 10,
            'Pacific Heights': 16
        },
        'Alamo Square': {
            'Haight-Ashbury': 5,
            'Russian Hill': 13,
            "Fisherman's Wharf": 19,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Pacific Heights': 10
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11,
            'Russian Hill': 7,
            "Fisherman's Wharf": 13,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Alamo Square': 10
        }
    }
    
    # Initial state
    initial_time = 9 * 60  # 9:00 AM
    initial_location = 'Haight-Ashbury'
    initial_met = set()
    initial_itinerary = []
    
    best_itinerary = find_best(
        initial_time, initial_location, initial_met, initial_itinerary, friends, travel_times
    )
    
    # Output as JSON
    result = {
        "itinerary": best_itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()