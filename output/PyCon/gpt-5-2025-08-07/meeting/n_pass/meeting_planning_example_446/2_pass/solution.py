import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = ['Richmond', 'Marina', 'Chinatown', 'Financial', 'Bayview', 'Union Square']
    
    # Travel times in minutes (matrix)
    travel_times = {
        ('Richmond', 'Marina'): 9,
        ('Richmond', 'Chinatown'): 20,
        ('Richmond', 'Financial'): 22,
        ('Richmond', 'Bayview'): 26,
        ('Richmond', 'Union Square'): 21,
        ('Marina', 'Richmond'): 11,
        ('Marina', 'Chinatown'): 16,
        ('Marina', 'Financial'): 17,
        ('Marina', 'Bayview'): 27,
        ('Marina', 'Union Square'): 16,
        ('Chinatown', 'Richmond'): 20,
        ('Chinatown', 'Marina'): 12,
        ('Chinatown', 'Financial'): 5,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Union Square'): 7,
        ('Financial', 'Richmond'): 21,
        ('Financial', 'Marina'): 15,
        ('Financial', 'Chinatown'): 5,
        ('Financial', 'Bayview'): 19,
        ('Financial', 'Union Square'): 9,
        ('Bayview', 'Richmond'): 25,
        ('Bayview', 'Marina'): 25,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Financial'): 19,
        ('Bayview', 'Union Square'): 17,
        ('Union Square', 'Richmond'): 20,
        ('Union Square', 'Marina'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Financial'): 9,
        ('Union Square', 'Bayview'): 15
    }
    
    # Friend constraints
    friends = {
        'Kimberly': {
            'location': 'Marina',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('16:45', '%H:%M'),
            'min_duration': 15
        },
        'Robert': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('12:15', '%H:%M'),
            'available_end': datetime.strptime('20:15', '%H:%M'),
            'min_duration': 15
        },
        'Rebecca': {
            'location': 'Financial',
            'available_start': datetime.strptime('13:15', '%H:%M'),
            'available_end': datetime.strptime('16:45', '%H:%M'),
            'min_duration': 75
        },
        'Margaret': {
            'location': 'Bayview',
            'available_start': datetime.strptime('9:30', '%H:%M'),
            'available_end': datetime.strptime('13:30', '%H:%M'),
            'min_duration': 30
        },
        'Kenneth': {
            'location': 'Union Square',
            'available_start': datetime.strptime('19:30', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 75
        }
    }
    
    # Start time
    start_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Richmond'
    
    def can_schedule_meeting(current_time, current_loc, friend_name, itinerary):
        """Check if we can schedule a meeting with this friend given current time and location"""
        friend = friends[friend_name]
        
        # Calculate travel time
        travel_time = travel_times.get((current_loc, friend['location']), 30)
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can arrive within available window
        if arrival_time < friend['available_start']:
            arrival_time = friend['available_start']
        elif arrival_time > friend['available_end']:
            return None, None, None
        
        # Calculate end time with minimum duration
        end_time = arrival_time + timedelta(minutes=friend['min_duration'])
        
        # Check if meeting fits within available window
        if end_time > friend['available_end']:
            return None, None, None
        
        return arrival_time, end_time, friend['location']
    
    def find_best_itinerary(current_time, current_loc, remaining_friends, current_itinerary, depth=0):
        """Recursive function to find the best itinerary"""
        if not remaining_friends:
            return current_itinerary[:]
        
        best_itinerary = current_itinerary[:]
        
        for i, friend in enumerate(remaining_friends):
            # Try to schedule this friend next
            arrival_time, end_time, new_loc = can_schedule_meeting(
                current_time, current_loc, friend, current_itinerary
            )
            
            if arrival_time is not None:
                # Add travel if needed
                new_itinerary = current_itinerary[:]
                
                if arrival_time > current_time:
                    new_itinerary.append({
                        "action": "travel",
                        "location": friends[friend]['location'],
                        "person": "",
                        "start_time": current_time.strftime('%H:%M'),
                        "end_time": arrival_time.strftime('%H:%M')
                    })
                
                # Add meeting
                new_itinerary.append({
                    "action": "meet",
                    "location": friends[friend]['location'],
                    "person": friend,
                    "start_time": arrival_time.strftime('%H:%M'),
                    "end_time": end_time.strftime('%H:%M')
                })
                
                # Recursively try remaining friends
                remaining = remaining_friends[:i] + remaining_friends[i+1:]
                candidate = find_best_itinerary(end_time, new_loc, remaining, new_itinerary, depth+1)
                
                # Keep the itinerary with most meetings (or longest total time)
                if len(candidate) > len(best_itinerary):
                    best_itinerary = candidate
        
        return best_itinerary
    
    # Try different orderings to find the best schedule
    friend_names = list(friends.keys())
    
    # Generate a few different orderings to try
    orderings = [
        friend_names,  # Original order
        sorted(friend_names, key=lambda x: friends[x]['available_start']),  # Earliest available first
        sorted(friend_names, key=lambda x: friends[x]['available_end']),  # Earliest ending first
        sorted(friend_names, key=lambda x: -friends[x]['min_duration']),  # Longest meetings first
    ]
    
    best_overall_itinerary = []
    
    for ordering in orderings:
        itinerary = find_best_itinerary(start_time, current_location, ordering, [])
        if len(itinerary) > len(best_overall_itinerary):
            best_overall_itinerary = itinerary
    
    # If no meetings found, try to find at least one meeting
    if not best_overall_itinerary:
        for friend in friend_names:
            arrival_time, end_time, new_loc = can_schedule_meeting(
                start_time, current_location, friend, []
            )
            if arrival_time is not None:
                itinerary = []
                if arrival_time > start_time:
                    itinerary.append({
                        "action": "travel",
                        "location": friends[friend]['location'],
                        "person": "",
                        "start_time": start_time.strftime('%H:%M'),
                        "end_time": arrival_time.strftime('%H:%M')
                    })
                
                itinerary.append({
                    "action": "meet",
                    "location": friends[friend]['location'],
                    "person": friend,
                    "start_time": arrival_time.strftime('%H:%M'),
                    "end_time": end_time.strftime('%H:%M')
                })
                
                if len(itinerary) > len(best_overall_itinerary):
                    best_overall_itinerary = itinerary
    
    # Output as JSON
    output = {"itinerary": best_overall_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()