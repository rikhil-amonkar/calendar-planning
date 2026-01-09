from constraint import Problem
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times between locations
    travel_times = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Fisherman\'s Wharf', 'The Castro'): 27,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Financial District'): 15,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Pacific Heights'): 16
    }

    # Define friend constraints
    friends = [
        {
            'name': 'William',
            'location': 'Alamo Square',
            'available_start': '15:15',
            'available_end': '17:15',
            'min_duration': 60
        },
        {
            'name': 'Joshua',
            'location': 'Richmond District',
            'available_start': '7:00',
            'available_end': '20:00',
            'min_duration': 15
        },
        {
            'name': 'Joseph',
            'location': 'Financial District',
            'available_start': '11:15',
            'available_end': '13:30',
            'min_duration': 15
        },
        {
            'name': 'David',
            'location': 'Union Square',
            'available_start': '16:45',
            'available_end': '19:15',
            'min_duration': 45
        },
        {
            'name': 'Brian',
            'location': 'Fisherman\'s Wharf',
            'available_start': '13:45',
            'available_end': '20:45',
            'min_duration': 105
        },
        {
            'name': 'Karen',
            'location': 'Marina District',
            'available_start': '11:30',
            'available_end': '18:30',
            'min_duration': 15
        },
        {
            'name': 'Anthony',
            'location': 'Haight-Ashbury',
            'available_start': '7:15',
            'available_end': '10:30',
            'min_duration': 30
        },
        {
            'name': 'Matthew',
            'location': 'Mission District',
            'available_start': '17:15',
            'available_end': '19:15',
            'min_duration': 120
        },
        {
            'name': 'Helen',
            'location': 'Pacific Heights',
            'available_start': '8:00',
            'available_end': '12:00',
            'min_duration': 75
        },
        {
            'name': 'Jeffrey',
            'location': 'Golden Gate Park',
            'available_start': '19:00',
            'available_end': '21:30',
            'min_duration': 60
        }
    ]

    # Create constraint problem
    problem = Problem()
    
    # Start time and location
    start_time = time_to_minutes('9:00')
    start_location = 'The Castro'
    
    # We'll use a simplified approach: try to visit friends in order
    # and build a feasible itinerary
    
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    # Try to visit each friend in a logical order based on availability windows
    # Sort by available start time to get a reasonable order
    available_friends = sorted(friends, key=lambda f: time_to_minutes(f['available_start']))
    
    for friend in available_friends:
        friend_location = friend['location']
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Calculate travel time
        travel_time = travel_times.get((current_location, friend_location), 30)
        
        # Earliest we can arrive at friend's location
        earliest_arrival = current_time + travel_time
        
        # If we arrive too early, we need to wait until they're available
        actual_start = max(earliest_arrival, available_start)
        
        # Check if we can complete the meeting within their availability
        if actual_start + min_duration <= available_end:
            # Add this meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": friend_location,
                "person": friend['name'],
                "start_time": minutes_to_time(actual_start),
                "end_time": minutes_to_time(actual_start + min_duration)
            })
            
            # Update current time and location
            current_time = actual_start + min_duration
            current_location = friend_location
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()