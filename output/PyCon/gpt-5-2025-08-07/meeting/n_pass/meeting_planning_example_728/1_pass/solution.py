import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Marina District': {
            'Mission District': 20, 'Fisherman\'s Wharf': 10, 'Presidio': 10,
            'Union Square': 16, 'Sunset District': 19, 'Financial District': 17,
            'Haight-Ashbury': 16, 'Russian Hill': 8
        },
        'Mission District': {
            'Marina District': 19, 'Fisherman\'s Wharf': 22, 'Presidio': 25,
            'Union Square': 15, 'Sunset District': 24, 'Financial District': 15,
            'Haight-Ashbury': 12, 'Russian Hill': 15
        },
        'Fisherman\'s Wharf': {
            'Marina District': 9, 'Mission District': 22, 'Presidio': 17,
            'Union Square': 13, 'Sunset District': 27, 'Financial District': 11,
            'Haight-Ashbury': 22, 'Russian Hill': 7
        },
        'Presidio': {
            'Marina District': 11, 'Mission District': 26, 'Fisherman\'s Wharf': 19,
            'Union Square': 22, 'Sunset District': 15, 'Financial District': 23,
            'Haight-Ashbury': 15, 'Russian Hill': 14
        },
        'Union Square': {
            'Marina District': 18, 'Mission District': 14, 'Fisherman\'s Wharf': 15,
            'Presidio': 24, 'Sunset District': 27, 'Financial District': 9,
            'Haight-Ashbury': 18, 'Russian Hill': 13
        },
        'Sunset District': {
            'Marina District': 21, 'Mission District': 25, 'Fisherman\'s Wharf': 29,
            'Presidio': 16, 'Union Square': 30, 'Financial District': 30,
            'Haight-Ashbury': 15, 'Russian Hill': 24
        },
        'Financial District': {
            'Marina District': 15, 'Mission District': 17, 'Fisherman\'s Wharf': 10,
            'Presidio': 22, 'Union Square': 9, 'Sunset District': 30,
            'Haight-Ashbury': 19, 'Russian Hill': 11
        },
        'Haight-Ashbury': {
            'Marina District': 17, 'Mission District': 11, 'Fisherman\'s Wharf': 23,
            'Presidio': 15, 'Union Square': 19, 'Sunset District': 15,
            'Financial District': 21, 'Russian Hill': 17
        },
        'Russian Hill': {
            'Marina District': 7, 'Mission District': 16, 'Fisherman\'s Wharf': 7,
            'Presidio': 14, 'Union Square': 10, 'Sunset District': 23,
            'Financial District': 11, 'Haight-Ashbury': 17
        }
    }

    # Define friends' availability and meeting requirements
    friends = {
        'Karen': {
            'location': 'Mission District',
            'start': datetime.strptime('14:15', '%H:%M'),
            'end': datetime.strptime('22:00', '%H:%M'),
            'duration': 30
        },
        'Richard': {
            'location': 'Fisherman\'s Wharf',
            'start': datetime.strptime('14:30', '%H:%M'),
            'end': datetime.strptime('17:30', '%H:%M'),
            'duration': 30
        },
        'Robert': {
            'location': 'Presidio',
            'start': datetime.strptime('21:45', '%H:%M'),
            'end': datetime.strptime('22:45', '%H:%M'),
            'duration': 60
        },
        'Joseph': {
            'location': 'Union Square',
            'start': datetime.strptime('11:45', '%H:%M'),
            'end': datetime.strptime('14:45', '%H:%M'),
            'duration': 120
        },
        'Helen': {
            'location': 'Sunset District',
            'start': datetime.strptime('14:45', '%H:%M'),
            'end': datetime.strptime('20:45', '%H:%M'),
            'duration': 105
        },
        'Elizabeth': {
            'location': 'Financial District',
            'start': datetime.strptime('10:00', '%H:%M'),
            'end': datetime.strptime('12:45', '%H:%M'),
            'duration': 75
        },
        'Kimberly': {
            'location': 'Haight-Ashbury',
            'start': datetime.strptime('14:15', '%H:%M'),
            'end': datetime.strptime('17:30', '%H:%M'),
            'duration': 105
        },
        'Ashley': {
            'location': 'Russian Hill',
            'start': datetime.strptime('11:30', '%H:%M'),
            'end': datetime.strptime('21:30', '%H:%M'),
            'duration': 45
        }
    }

    # Convert times to minutes since 9:00 AM for easier computation
    base_time = datetime.strptime('9:00', '%H:%M')
    
    def time_to_minutes(t):
        return int((t - base_time).total_seconds() / 60)
    
    def minutes_to_time_str(minutes):
        time_obj = base_time + timedelta(minutes=minutes)
        return time_obj.strftime('%H:%M').lstrip('0') if time_obj.strftime('%H:%M').startswith('0') else time_obj.strftime('%H:%M')

    # Create problem instance
    problem = constraint.Problem()
    
    # Define variables for each friend: start time and whether we meet them (1) or not (0)
    friend_names = list(friends.keys())
    
    for friend in friend_names:
        info = friends[friend]
        start_min = time_to_minutes(info['start'])
        end_min = time_to_minutes(info['end'])
        duration = info['duration']
        
        # We can choose to meet this friend or not, and if we do, we need to schedule the meeting
        problem.addVariable(f'{friend}_meet', [0, 1])
        # Start time if we meet them (within their availability window, accounting for duration)
        problem.addVariable(f'{friend}_start', range(start_min, end_min - duration + 1))
    
    # Add constraints for travel time between consecutive meetings
    # We need to determine the order of meetings
    # For simplicity, we'll try all permutations and find a feasible schedule
    
    # This is a complex scheduling problem that would typically require a more sophisticated approach
    # For this example, we'll use a greedy approach to find a feasible schedule
    
    # Start at Marina District at 9:00
    current_location = 'Marina District'
    current_time = time_to_minutes(base_time)
    end_of_day = time_to_minutes(datetime.strptime('23:00', '%H:%M'))  # Assume day ends at 11 PM
    
    itinerary = []
    remaining_friends = friend_names.copy()
    
    # Try to schedule meetings in a greedy manner
    while remaining_friends and current_time < end_of_day:
        best_friend = None
        best_start_time = None
        best_travel_time = float('inf')
        
        for friend in remaining_friends:
            info = friends[friend]
            location = info['location']
            duration = info['duration']
            
            # Calculate travel time
            travel_time = travel_times[current_location][location]
            
            # Earliest we can start meeting this friend
            earliest_start = current_time + travel_time
            friend_start_min = time_to_minutes(info['start'])
            friend_end_min = time_to_minutes(info['end'])
            
            # Check if we can schedule this meeting
            if earliest_start <= friend_end_min - duration:
                # We can meet this friend
                start_time = max(earliest_start, friend_start_min)
                
                # Prefer friends with shorter travel time
                if travel_time < best_travel_time:
                    best_friend = friend
                    best_start_time = start_time
                    best_travel_time = travel_time
        
        if best_friend is None:
            # No more meetings can be scheduled
            break
        
        # Schedule the meeting
        info = friends[best_friend]
        duration = info['duration']
        end_time = best_start_time + duration
        
        itinerary.append({
            'action': 'meet',
            'location': info['location'],
            'person': best_friend,
            'start_time': minutes_to_time_str(best_start_time),
            'end_time': minutes_to_time_str(end_time)
        })
        
        # Update current state
        current_location = info['location']
        current_time = end_time
        remaining_friends.remove(best_friend)
    
    # Output the result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()