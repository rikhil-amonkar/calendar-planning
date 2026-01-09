from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Marina District'): 25,
        ('Bayview', 'Embarcadero'): 19,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Embarcadero'): 14,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Marina District'): 12
    }

    # Friend availability constraints
    friends = {
        'Thomas': {
            'location': 'Bayview',
            'start': datetime.strptime('15:30', '%H:%M'),
            'end': datetime.strptime('18:30', '%H:%M'),
            'min_duration': 120
        },
        'Stephanie': {
            'location': 'Golden Gate Park',
            'start': datetime.strptime('18:30', '%H:%M'),
            'end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 30
        },
        'Laura': {
            'location': 'Nob Hill',
            'start': datetime.strptime('8:45', '%H:%M'),
            'end': datetime.strptime('16:15', '%H:%M'),
            'min_duration': 30
        },
        'Betty': {
            'location': 'Marina District',
            'start': datetime.strptime('18:45', '%H:%M'),
            'end': datetime.strptime('21:45', '%H:%M'),
            'min_duration': 45
        },
        'Patricia': {
            'location': 'Embarcadero',
            'start': datetime.strptime('17:30', '%H:%M'),
            'end': datetime.strptime('22:00', '%H:%M'),
            'min_duration': 45
        }
    }

    # Start location and time
    start_location = 'Fisherman\'s Wharf'
    start_time = datetime.strptime('9:00', '%H:%M')

    def find_best_itinerary(current_time, current_location, remaining_friends, current_itinerary, best_result):
        """Recursive function to find the best itinerary"""
        if len(remaining_friends) == 0:
            if len(current_itinerary) > len(best_result['itinerary']):
                best_result['itinerary'] = current_itinerary.copy()
            return
        
        for i, friend in enumerate(remaining_friends):
            friend_data = friends[friend]
            location = friend_data['location']
            
            # Calculate travel time
            travel_time = travel_times.get((current_location, location), 999)
            
            # Calculate arrival time
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            # Check if we can meet this friend
            if arrival_time <= friend_data['end']:
                # Calculate meeting start time (can't start before friend's availability)
                meeting_start = max(arrival_time, friend_data['start'])
                
                # Calculate meeting end time
                meeting_end = meeting_start + timedelta(minutes=friend_data['min_duration'])
                
                # Check if meeting fits within friend's availability
                if meeting_end <= friend_data['end']:
                    # Add this meeting to itinerary
                    new_itinerary_item = {
                        "action": "meet",
                        "location": location,
                        "person": friend,
                        "start_time": meeting_start.strftime('%H:%M').lstrip('0').replace(':0', ':'),
                        "end_time": meeting_end.strftime('%H:%M').lstrip('0').replace(':0', ':')
                    }
                    
                    current_itinerary.append(new_itinerary_item)
                    
                    # Recursively try remaining friends
                    new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                    find_best_itinerary(meeting_end, location, new_remaining, current_itinerary, best_result)
                    
                    # Backtrack
                    current_itinerary.pop()
        
        # Also try skipping this friend (but only if we haven't found a complete solution)
        if len(current_itinerary) > 0:
            new_remaining = remaining_friends[1:]
            find_best_itinerary(current_time, current_location, new_remaining, current_itinerary, best_result)

    # Find the best itinerary
    best_result = {'itinerary': []}
    all_friends = list(friends.keys())
    
    # Try different starting points to maximize number of meetings
    find_best_itinerary(start_time, start_location, all_friends, [], best_result)
    
    # If no solution found with all friends, try with subsets
    if len(best_result['itinerary']) == 0:
        for i in range(len(all_friends)-1, 0, -1):
            from itertools import combinations
            for friend_subset in combinations(all_friends, i):
                find_best_itinerary(start_time, start_location, list(friend_subset), [], best_result)
                if len(best_result['itinerary']) > 0:
                    break
            if len(best_result['itinerary']) > 0:
                break

    print(json.dumps(best_result, indent=2))

if __name__ == "__main__":
    main()