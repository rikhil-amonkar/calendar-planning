import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'The Castro'): 13
    }

    # Friend constraints
    friends = {
        'Emily': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('19:00', '%H:%M'),
            'available_end': datetime.strptime('21:00', '%H:%M'),
            'min_duration': 15
        },
        'Margaret': {
            'location': 'Financial District',
            'available_start': datetime.strptime('16:30', '%H:%M'),
            'available_end': datetime.strptime('20:15', '%H:%M'),
            'min_duration': 75
        },
        'Ronald': {
            'location': 'North Beach',
            'available_start': datetime.strptime('18:30', '%H:%M'),
            'available_end': datetime.strptime('19:30', '%H:%M'),
            'min_duration': 45
        },
        'Deborah': {
            'location': 'The Castro',
            'available_start': datetime.strptime('13:45', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 90
        },
        'Jeffrey': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('11:15', '%H:%M'),
            'available_end': datetime.strptime('14:30', '%H:%M'),
            'min_duration': 120
        }
    }

    # Start at Nob Hill at 9:00 AM
    current_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Nob Hill'
    end_of_day = datetime.strptime('21:00', '%H:%M')
    
    itinerary = []
    
    # Sort friends by their availability start time to prioritize earlier meetings
    sorted_friends = sorted(friends.items(), key=lambda x: x[1]['available_start'])
    
    for friend_name, friend_info in sorted_friends:
        location = friend_info['location']
        min_duration = friend_info['min_duration']
        available_start = friend_info['available_start']
        available_end = friend_info['available_end']
        
        # Calculate travel time to this friend
        travel_time = travel_times.get((current_location, location), 0)
        
        # Calculate earliest possible start time (after travel)
        earliest_start = current_time + timedelta(minutes=travel_time)
        
        # If we arrive before their availability starts, wait until they're available
        if earliest_start < available_start:
            potential_start = available_start
        else:
            potential_start = earliest_start
        
        # Check if we can fit this meeting within their availability and before end of day
        potential_end = potential_start + timedelta(minutes=min_duration)
        
        if (potential_start >= available_start and 
            potential_end <= available_end and 
            potential_end <= end_of_day):
            
            # Add this meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend_name,
                "start_time": potential_start.strftime('%H:%M'),
                "end_time": potential_end.strftime('%H:%M')
            })
            
            # Update current time and location
            current_time = potential_end
            current_location = location
    
    # If we couldn't schedule all friends, try to optimize by checking different orders
    if len(itinerary) < len(friends):
        # Try different ordering strategies
        strategies = [
            # Sort by available start time (already tried)
            sorted(friends.items(), key=lambda x: x[1]['available_start']),
            # Sort by available end time
            sorted(friends.items(), key=lambda x: x[1]['available_end']),
            # Sort by duration (shortest first)
            sorted(friends.items(), key=lambda x: x[1]['min_duration']),
            # Sort by location proximity to current location
            sorted(friends.items(), key=lambda x: travel_times.get((current_location, x[1]['location']), float('inf')))
        ]
        
        best_itinerary = itinerary
        best_count = len(itinerary)
        
        for strategy in strategies[1:]:  # Skip first strategy (already tried)
            current_time = datetime.strptime('9:00', '%H:%M')
            current_location = 'Nob Hill'
            temp_itinerary = []
            
            for friend_name, friend_info in strategy:
                location = friend_info['location']
                min_duration = friend_info['min_duration']
                available_start = friend_info['available_start']
                available_end = friend_info['available_end']
                
                travel_time = travel_times.get((current_location, location), 0)
                earliest_start = current_time + timedelta(minutes=travel_time)
                
                if earliest_start < available_start:
                    potential_start = available_start
                else:
                    potential_start = earliest_start
                
                potential_end = potential_start + timedelta(minutes=min_duration)
                
                if (potential_start >= available_start and 
                    potential_end <= available_end and 
                    potential_end <= end_of_day):
                    
                    temp_itinerary.append({
                        "action": "meet",
                        "location": location,
                        "person": friend_name,
                        "start_time": potential_start.strftime('%H:%M'),
                        "end_time": potential_end.strftime('%H:%M')
                    })
                    
                    current_time = potential_end
                    current_location = location
            
            if len(temp_itinerary) > best_count:
                best_itinerary = temp_itinerary
                best_count = len(temp_itinerary)
        
        itinerary = best_itinerary

    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()