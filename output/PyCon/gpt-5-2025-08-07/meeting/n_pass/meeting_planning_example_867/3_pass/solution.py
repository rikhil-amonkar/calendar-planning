import json
from itertools import permutations

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Haight-Ashbury': {
            'Mission District': 11, 'Union Square': 19, 'Pacific Heights': 12, 
            'Bayview': 18, 'Fisherman\'s Wharf': 23, 'Marina District': 17,
            'Richmond District': 10, 'Sunset District': 15, 'Golden Gate Park': 7
        },
        'Mission District': {
            'Haight-Ashbury': 12, 'Union Square': 15, 'Pacific Heights': 16,
            'Bayview': 14, 'Fisherman\'s Wharf': 22, 'Marina District': 19,
            'Richmond District': 20, 'Sunset District': 24, 'Golden Gate Park': 17
        },
        'Union Square': {
            'Haight-Ashbury': 18, 'Mission District': 14, 'Pacific Heights': 15,
            'Bayview': 15, 'Fisherman\'s Wharf': 15, 'Marina District': 18,
            'Richmond District': 20, 'Sunset District': 27, 'Golden Gate Park': 22
        },
        'Pacific Heights': {
            'Haight-Ashbury': 11, 'Mission District': 15, 'Union Square': 12,
            'Bayview': 22, 'Fisherman\'s Wharf': 13, 'Marina District': 6,
            'Richmond District': 12, 'Sunset District': 21, 'Golden Gate Park': 15
        },
        'Bayview': {
            'Haight-Ashbury': 19, 'Mission District': 13, 'Union Square': 18,
            'Pacific Heights': 23, 'Fisherman\'s Wharf': 25, 'Marina District': 27,
            'Richmond District': 25, 'Sunset District': 23, 'Golden Gate Park': 22
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22, 'Mission District': 22, 'Union Square': 13,
            'Pacific Heights': 12, 'Bayview': 26, 'Marina District': 9,
            'Richmond District': 18, 'Sunset District': 27, 'Golden Gate Park': 25
        },
        'Marina District': {
            'Haight-Ashbury': 16, 'Mission District': 20, 'Union Square': 16,
            'Pacific Heights': 7, 'Bayview': 27, 'Fisherman\'s Wharf': 10,
            'Richmond District': 11, 'Sunset District': 19, 'Golden Gate Park': 18
        },
        'Richmond District': {
            'Haight-Ashbury': 10, 'Mission District': 20, 'Union Square': 21,
            'Pacific Heights': 10, 'Bayview': 27, 'Fisherman\'s Wharf': 18,
            'Marina District': 9, 'Sunset District': 11, 'Golden Gate Park': 9
        },
        'Sunset District': {
            'Haight-Ashbury': 15, 'Mission District': 25, 'Union Square': 30,
            'Pacific Heights': 21, 'Bayview': 22, 'Fisherman\'s Wharf': 29,
            'Marina District': 21, 'Richmond District': 12, 'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Haight-Ashbury': 7, 'Mission District': 17, 'Union Square': 22,
            'Pacific Heights': 16, 'Bayview': 23, 'Fisherman\'s Wharf': 24,
            'Marina District': 16, 'Richmond District': 7, 'Sunset District': 10
        }
    }

    # Define friends' availability and meeting requirements
    friends = [
        {'name': 'Elizabeth', 'location': 'Mission District', 'start': 10.5, 'end': 20.0, 'duration': 1.5},
        {'name': 'David', 'location': 'Union Square', 'start': 15.25, 'end': 19.0, 'duration': 0.75},
        {'name': 'Sandra', 'location': 'Pacific Heights', 'start': 7.0, 'end': 20.0, 'duration': 2.0},
        {'name': 'Thomas', 'location': 'Bayview', 'start': 19.5, 'end': 20.5, 'duration': 0.5},
        {'name': 'Robert', 'location': 'Fisherman\'s Wharf', 'start': 10.0, 'end': 15.0, 'duration': 0.25},
        {'name': 'Kenneth', 'location': 'Marina District', 'start': 10.75, 'end': 13.0, 'duration': 0.75},
        {'name': 'Melissa', 'location': 'Richmond District', 'start': 18.25, 'end': 20.0, 'duration': 0.25},
        {'name': 'Kimberly', 'location': 'Sunset District', 'start': 10.25, 'end': 18.25, 'duration': 1.75},
        {'name': 'Amanda', 'location': 'Golden Gate Park', 'start': 7.75, 'end': 18.75, 'duration': 0.25}
    ]

    def find_feasible_schedule(current_path, remaining_friends, current_time, current_location):
        """Recursive function to find a feasible schedule using backtracking."""
        if not remaining_friends:
            return current_path
        
        # Try friends in order of earliest possible meeting time
        for i, friend in enumerate(remaining_friends):
            # Calculate travel time from current location
            travel_time = travel_times[current_location][friend['location']] / 60.0
            
            # Calculate earliest possible start time
            earliest_start = max(current_time + travel_time, friend['start'])
            
            # Check if meeting is feasible
            if earliest_start + friend['duration'] <= friend['end']:
                # Create new path with this friend
                new_path = current_path + [{
                    'friend': friend,
                    'start_time': earliest_start,
                    'end_time': earliest_start + friend['duration']
                }]
                
                # Recursively try remaining friends
                new_remaining = remaining_friends[:i] + remaining_friends[i+1:]
                result = find_feasible_schedule(
                    new_path, new_remaining, earliest_start + friend['duration'], friend['location']
                )
                
                if result:
                    return result
        
        return None

    def convert_to_itinerary(schedule):
        """Convert the schedule to the required itinerary format."""
        itinerary = []
        for meeting in schedule:
            friend = meeting['friend']
            start_time = meeting['start_time']
            end_time = meeting['end_time']
            
            # Convert decimal hours to time string
            start_hour = int(start_time)
            start_minute = int(round((start_time - start_hour) * 60))
            end_hour = int(end_time)
            end_minute = int(round((end_time - end_hour) * 60))
            
            # Handle minute overflow
            if start_minute == 60:
                start_hour += 1
                start_minute = 0
            if end_minute == 60:
                end_hour += 1
                end_minute = 0
            
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str
            })
        
        return itinerary

    # Try different starting orders to find a feasible schedule
    # Start with friends who have tighter time windows first
    sorted_friends = sorted(friends, key=lambda x: (x['end'] - x['start'], x['start']))
    
    # Start from Haight-Ashbury at 9:00
    start_time = 9.0
    start_location = 'Haight-Ashbury'
    
    # Try to find a feasible schedule
    schedule = find_feasible_schedule([], sorted_friends, start_time, start_location)
    
    if schedule:
        itinerary = convert_to_itinerary(schedule)
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If no schedule found with sorted order, try with original order
        schedule = find_feasible_schedule([], friends, start_time, start_location)
        if schedule:
            itinerary = convert_to_itinerary(schedule)
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
        else:
            print('{"itinerary": []}')

if __name__ == "__main__":
    main()