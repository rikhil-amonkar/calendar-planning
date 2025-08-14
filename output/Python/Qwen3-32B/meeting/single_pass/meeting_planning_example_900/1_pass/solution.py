import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times between locations
    travel_times = {
        'Richmond District': {
            'The Castro': 16,
            'Nob Hill': 17,
            'Marina District': 9,
            'Pacific Heights': 10,
            'Haight-Ashbury': 10,
            'Mission District': 20,
            'Chinatown': 20,
            'Russian Hill': 13,
            'Alamo Square': 13,
            'Bayview': 27
        },
        'The Castro': {
            'Richmond District': 16,
            'Nob Hill': 16,
            'Marina District': 21,
            'Pacific Heights': 16,
            'Haight-Ashbury': 6,
            'Mission District': 7,
            'Chinatown': 22,
            'Russian Hill': 18,
            'Alamo Square': 8,
            'Bayview': 19
        },
        'Nob Hill': {
            'Richmond District': 14,
            'The Castro': 17,
            'Marina District': 11,
            'Pacific Heights': 8,
            'Haight-Ashbury': 13,
            'Mission District': 13,
            'Chinatown': 6,
            'Russian Hill': 5,
            'Alamo Square': 11,
            'Bayview': 19
        },
        'Marina District': {
            'Richmond District': 11,
            'The Castro': 22,
            'Nob Hill': 12,
            'Pacific Heights': 7,
            'Haight-Ashbury': 16,
            'Mission District': 20,
            'Chinatown': 15,
            'Russian Hill': 8,
            'Alamo Square': 15,
            'Bayview': 27
        },
        'Pacific Heights': {
            'Richmond District': 12,
            'The Castro': 16,
            'Nob Hill': 8,
            'Marina District': 6,
            'Haight-Ashbury': 11,
            'Mission District': 15,
            'Chinatown': 11,
            'Russian Hill': 7,
            'Alamo Square': 10,
            'Bayview': 22
        },
        'Haight-Ashbury': {
            'Richmond District': 10,
            'The Castro': 6,
            'Nob Hill': 15,
            'Marina District': 17,
            'Pacific Heights': 12,
            'Mission District': 11,
            'Chinatown': 19,
            'Russian Hill': 17,
            'Alamo Square': 5,
            'Bayview': 18
        },
        'Mission District': {
            'Richmond District': 20,
            'The Castro': 7,
            'Nob Hill': 12,
            'Marina District': 19,
            'Pacific Heights': 16,
            'Haight-Ashbury': 12,
            'Chinatown': 16,
            'Russian Hill': 15,
            'Alamo Square': 11,
            'Bayview': 14
        },
        'Chinatown': {
            'Richmond District': 20,
            'The Castro': 22,
            'Nob Hill': 9,
            'Marina District': 12,
            'Pacific Heights': 10,
            'Haight-Ashbury': 19,
            'Mission District': 17,
            'Russian Hill': 7,
            'Alamo Square': 17,
            'Bayview': 20
        },
        'Russian Hill': {
            'Richmond District': 14,
            'The Castro': 21,
            'Nob Hill': 5,
            'Marina District': 7,
            'Pacific Heights': 7,
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Chinatown': 9,
            'Alamo Square': 15,
            'Bayview': 23
        },
        'Alamo Square': {
            'Richmond District': 11,
            'The Castro': 8,
            'Nob Hill': 11,
            'Marina District': 15,
            'Pacific Heights': 10,
            'Haight-Ashbury': 5,
            'Mission District': 10,
            'Chinatown': 15,
            'Russian Hill': 13,
            'Bayview': 16
        },
        'Bayview': {
            'Richmond District': 25,
            'The Castro': 19,
            'Nob Hill': 20,
            'Marina District': 27,
            'Pacific Heights': 23,
            'Haight-Ashbury': 19,
            'Mission District': 13,
            'Chinatown': 19,
            'Russian Hill': 23,
            'Alamo Square': 16
        }
    }

    # Define friends with their constraints
    friends = [
        {
            'name': 'Matthew',
            'location': 'The Castro',
            'available_start': '16:30',
            'available_end': '20:00',
            'required_duration': 45
        },
        {
            'name': 'Rebecca',
            'location': 'Nob Hill',
            'available_start': '15:15',
            'available_end': '19:15',
            'required_duration': 105
        },
        {
            'name': 'Brian',
            'location': 'Marina District',
            'available_start': '14:15',
            'available_end': '22:00',
            'required_duration': 30
        },
        {
            'name': 'Emily',
            'location': 'Pacific Heights',
            'available_start': '11:15',
            'available_end': '19:45',
            'required_duration': 15
        },
        {
            'name': 'Karen',
            'location': 'Haight-Ashbury',
            'available_start': '11:45',
            'available_end': '17:30',
            'required_duration': 30
        },
        {
            'name': 'Stephanie',
            'location': 'Mission District',
            'available_start': '13:00',
            'available_end': '15:45',
            'required_duration': 75
        },
        {
            'name': 'James',
            'location': 'Chinatown',
            'available_start': '14:30',
            'available_end': '19:00',
            'required_duration': 120
        },
        {
            'name': 'Steven',
            'location': 'Russian Hill',
            'available_start': '14:00',
            'available_end': '20:00',
            'required_duration': 30
        },
        {
            'name': 'Elizabeth',
            'location': 'Alamo Square',
            'available_start': '13:00',
            'available_end': '17:15',
            'required_duration': 120
        },
        {
            'name': 'William',
            'location': 'Bayview',
            'available_start': '18:15',
            'available_end': '20:15',
            'required_duration': 90
        }
    ]

    # Preprocess friends to add computed time fields
    feasible_friends = []
    for friend in friends:
        available_start = time_str_to_minutes(friend['available_start'])
        available_end = time_str_to_minutes(friend['available_end'])
        required_duration = friend['required_duration']
        latest_start = available_end - required_duration
        
        if latest_start >= available_start:
            friend['available_start_min'] = available_start
            friend['available_end_min'] = available_end
            friend['latest_start'] = latest_start
            feasible_friends.append(friend)
    
    # Sort friends by latest_start (earliest deadline first)
    feasible_friends.sort(key=lambda x: x['latest_start'])
    
    # Initialize schedule parameters
    current_time = time_str_to_minutes('9:00')  # Start at 9:00 AM
    current_location = 'Richmond District'
    itinerary = []
    
    # Calculate optimal schedule
    for friend in feasible_friends:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Determine earliest possible meeting start time
        earliest_start = max(arrival_time, friend['available_start_min'])
        
        # Check if meeting is possible within constraints
        if earliest_start + friend['required_duration'] <= friend['latest_start']:
            # Schedule the meeting
            meeting_start = earliest_start
            meeting_end = meeting_start + friend['required_duration']
            
            # Convert to time strings
            start_str = minutes_to_time_str(meeting_start)
            end_str = minutes_to_time_str(meeting_end)
            
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': start_str,
                'end_time': end_str
            })
            
            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']
    
    # Output result in JSON format
    result = {
        'itinerary': itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()