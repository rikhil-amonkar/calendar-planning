from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Sunset District'): 25,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Sunset District'): 15
    }
    
    # Friend constraints
    friends = {
        'Ronald': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('10:00', '%H:%M'),
            'available_end': datetime.strptime('17:00', '%H:%M'),
            'min_duration': 105
        },
        'Sarah': {
            'location': 'Russian Hill',
            'available_start': datetime.strptime('7:15', '%H:%M'),
            'available_end': datetime.strptime('9:30', '%H:%M'),
            'min_duration': 45
        },
        'Helen': {
            'location': 'The Castro',
            'available_start': datetime.strptime('13:30', '%H:%M'),
            'available_end': datetime.strptime('17:00', '%H:%M'),
            'min_duration': 120
        },
        'Joshua': {
            'location': 'Sunset District',
            'available_start': datetime.strptime('14:15', '%H:%M'),
            'available_end': datetime.strptime('19:30', '%H:%M'),
            'min_duration': 90
        },
        'Margaret': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('10:15', '%H:%M'),
            'available_end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 60
        }
    }
    
    # Start at Pacific Heights at 9:00 AM
    start_time = datetime.strptime('9:00', '%H:%M')
    
    # Define the preferred visit order
    visit_order = ['Sarah', 'Ronald', 'Margaret', 'Helen', 'Joshua']
    
    def can_visit_friend(current_time, current_location, friend_name):
        """Check if we can visit a friend given current time and location"""
        friend = friends[friend_name]
        
        # Calculate travel time
        travel_time = travel_times.get((current_location, friend['location']))
        if travel_time is None:
            return None
        
        # Calculate arrival time
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we arrive within available window
        if arrival_time > friend['available_end']:
            return None
        
        # Determine meeting start time (can't start before friend is available)
        meeting_start = max(arrival_time, friend['available_start'])
        
        # Check if we have enough time for minimum duration
        if meeting_start + timedelta(minutes=friend['min_duration']) > friend['available_end']:
            return None
        
        # Calculate meeting end time
        meeting_end = meeting_start + timedelta(minutes=friend['min_duration'])
        
        return {
            'start': meeting_start,
            'end': meeting_end,
            'location': friend['location']
        }
    
    def find_schedule(current_time, current_location, remaining_friends, current_itinerary, best_schedule):
        """Recursive function to find the best schedule"""
        if not remaining_friends:
            # Found a complete schedule
            if len(current_itinerary) > len(best_schedule['itinerary']):
                best_schedule['itinerary'] = current_itinerary.copy()
            return
        
        for i, friend_name in enumerate(remaining_friends):
            # Try to visit this friend next
            visit_result = can_visit_friend(current_time, current_location, friend_name)
            
            if visit_result:
                # Add this visit to itinerary
                visit_entry = {
                    "action": "meet",
                    "location": friends[friend_name]['location'],
                    "person": friend_name,
                    "start_time": visit_result['start'].strftime('%H:%M'),
                    "end_time": visit_result['end'].strftime('%H:%M')
                }
                
                current_itinerary.append(visit_entry)
                
                # Recursively try remaining friends
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                find_schedule(visit_result['end'], visit_result['location'], 
                            new_remaining, current_itinerary, best_schedule)
                
                # Backtrack
                current_itinerary.pop()
    
    # Try to find the best schedule
    best_schedule = {'itinerary': []}
    
    # First, try the preferred order
    find_schedule(start_time, 'Pacific Heights', visit_order, [], best_schedule)
    
    # If preferred order doesn't work, try all permutations for smaller subsets
    if len(best_schedule['itinerary']) < len(visit_order):
        import itertools
        
        # Try different orders to maximize number of friends visited
        for perm in itertools.permutations(visit_order):
            if len(perm) <= len(best_schedule['itinerary']):
                continue  # Skip if we can't get more friends than current best
            
            find_schedule(start_time, 'Pacific Heights', list(perm), [], best_schedule)
            
            # Early exit if we found a complete schedule
            if len(best_schedule['itinerary']) == len(visit_order):
                break
    
    # Format the result
    result = {"itinerary": best_schedule['itinerary']}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()