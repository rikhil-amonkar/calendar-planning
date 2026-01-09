from constraint import Problem, AllDifferentConstraint
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if ':' not in time_str:
        return int(time_str) * 60
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times matrix (in minutes)
    travel_times = {
        'The Castro': {
            'Marina District': 21, 'Presidio': 20, 'North Beach': 20, 'Embarcadero': 22,
            'Haight-Ashbury': 6, 'Golden Gate Park': 11, 'Richmond District': 16,
            'Alamo Square': 8, 'Financial District': 21, 'Sunset District': 17
        },
        'Marina District': {
            'The Castro': 22, 'Presidio': 10, 'North Beach': 11, 'Embarcadero': 14,
            'Haight-Ashbury': 16, 'Golden Gate Park': 18, 'Richmond District': 11,
            'Alamo Square': 15, 'Financial District': 17, 'Sunset District': 19
        },
        'Presidio': {
            'The Castro': 21, 'Marina District': 11, 'North Beach': 18, 'Embarcadero': 20,
            'Haight-Ashbury': 15, 'Golden Gate Park': 12, 'Richmond District': 7,
            'Alamo Square': 19, 'Financial District': 23, 'Sunset District': 15
        },
        'North Beach': {
            'The Castro': 23, 'Marina District': 9, 'Presidio': 17, 'Embarcadero': 6,
            'Haight-Ashbury': 18, 'Golden Gate Park': 22, 'Richmond District': 18,
            'Alamo Square': 16, 'Financial District': 8, 'Sunset District': 27
        },
        'Embarcadero': {
            'The Castro': 25, 'Marina District': 12, 'Presidio': 20, 'North Beach': 5,
            'Haight-Ashbury': 21, 'Golden Gate Park': 25, 'Richmond District': 21,
            'Alamo Square': 19, 'Financial District': 5, 'Sunset District': 30
        },
        'Haight-Ashbury': {
            'The Castro': 6, 'Marina District': 17, 'Presidio': 15, 'North Beach': 19,
            'Embarcadero': 20, 'Golden Gate Park': 7, 'Richmond District': 10,
            'Alamo Square': 5, 'Financial District': 21, 'Sunset District': 15
        },
        'Golden Gate Park': {
            'The Castro': 13, 'Marina District': 16, 'Presidio': 11, 'North Beach': 23,
            'Embarcadero': 25, 'Haight-Ashbury': 7, 'Richmond District': 7,
            'Alamo Square': 9, 'Financial District': 26, 'Sunset District': 10
        },
        'Richmond District': {
            'The Castro': 16, 'Marina District': 9, 'Presidio': 7, 'North Beach': 17,
            'Embarcadero': 19, 'Haight-Ashbury': 10, 'Golden Gate Park': 9,
            'Alamo Square': 13, 'Financial District': 22, 'Sunset District': 11
        },
        'Alamo Square': {
            'The Castro': 8, 'Marina District': 15, 'Presidio': 17, 'North Beach': 15,
            'Embarcadero': 16, 'Haight-Ashbury': 5, 'Golden Gate Park': 9,
            'Richmond District': 11, 'Financial District': 17, 'Sunset District': 16
        },
        'Financial District': {
            'The Castro': 20, 'Marina District': 15, 'Presidio': 22, 'North Beach': 7,
            'Embarcadero': 4, 'Haight-Ashbury': 19, 'Golden Gate Park': 23,
            'Richmond District': 21, 'Alamo Square': 17, 'Sunset District': 30
        },
        'Sunset District': {
            'The Castro': 17, 'Marina District': 21, 'Presidio': 16, 'North Beach': 28,
            'Embarcadero': 30, 'Haight-Ashbury': 15, 'Golden Gate Park': 11,
            'Richmond District': 12, 'Alamo Square': 17, 'Financial District': 30
        }
    }

    # Friend constraints
    friends = [
        {'name': 'Elizabeth', 'location': 'Marina District', 'available_start': '19:00', 'available_end': '20:45', 'min_duration': 105},
        {'name': 'Joshua', 'location': 'Presidio', 'available_start': '8:30', 'available_end': '13:15', 'min_duration': 105},
        {'name': 'Timothy', 'location': 'North Beach', 'available_start': '19:45', 'available_end': '22:00', 'min_duration': 90},
        {'name': 'David', 'location': 'Embarcadero', 'available_start': '10:45', 'available_end': '12:30', 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'available_start': '16:45', 'available_end': '21:30', 'min_duration': 75},
        {'name': 'Lisa', 'location': 'Golden Gate Park', 'available_start': '17:30', 'available_end': '21:45', 'min_duration': 45},
        {'name': 'Ronald', 'location': 'Richmond District', 'available_start': '8:00', 'available_end': '9:30', 'min_duration': 90},
        {'name': 'Stephanie', 'location': 'Alamo Square', 'available_start': '15:30', 'available_end': '16:30', 'min_duration': 30},
        {'name': 'Helen', 'location': 'Financial District', 'available_start': '17:30', 'available_end': '18:30', 'min_duration': 45},
        {'name': 'Laura', 'location': 'Sunset District', 'available_start': '17:45', 'available_end': '21:15', 'min_duration': 90}
    ]

    # Convert all times to minutes
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])

    # Start at The Castro at 9:00 AM
    current_time = time_to_minutes('9:00')
    current_location = 'The Castro'
    itinerary = []

    # Sort friends by availability start time for a simple greedy approach
    sorted_friends = sorted(friends, key=lambda x: x['available_start_min'])

    for friend in sorted_friends:
        # Calculate travel time to friend's location
        travel_time = travel_times[current_location][friend['location']]
        
        # Calculate earliest possible start time (after travel)
        earliest_start = current_time + travel_time
        
        # Ensure we don't start before friend is available
        actual_start = max(earliest_start, friend['available_start_min'])
        
        # Calculate end time based on minimum duration
        actual_end = actual_start + friend['min_duration']
        
        # Ensure we don't exceed friend's availability
        if actual_end <= friend['available_end_min']:
            # Add meeting to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(actual_start),
                'end_time': minutes_to_time(actual_end)
            })
            
            # Update current time and location
            current_time = actual_end
            current_location = friend['location']

    # Output result as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()