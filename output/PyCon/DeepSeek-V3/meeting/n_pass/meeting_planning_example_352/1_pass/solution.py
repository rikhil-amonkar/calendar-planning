import constraint
import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Marina District'): 18,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Marina District'): 11,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Nob Hill'): 8,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Chinatown'): 16
    }
    
    # Friend constraints
    friends = {
        'Karen': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('21:15', '%H:%M'),  # 9:15 PM
            'available_end': datetime.strptime('21:45', '%H:%M'),    # 9:45 PM
            'min_duration': 30  # minutes
        },
        'Joseph': {
            'location': 'Haight-Ashbury',
            'available_start': datetime.strptime('12:30', '%H:%M'),  # 12:30 PM
            'available_end': datetime.strptime('19:45', '%H:%M'),    # 7:45 PM
            'min_duration': 90  # minutes
        },
        'Sandra': {
            'location': 'Chinatown',
            'available_start': datetime.strptime('7:15', '%H:%M'),   # 7:15 AM
            'available_end': datetime.strptime('19:15', '%H:%M'),    # 7:15 PM
            'min_duration': 75  # minutes
        },
        'Nancy': {
            'location': 'Marina District',
            'available_start': datetime.strptime('11:00', '%H:%M'),  # 11:00 AM
            'available_end': datetime.strptime('20:15', '%H:%M'),    # 8:15 PM
            'min_duration': 105  # minutes
        }
    }
    
    # Start at Union Square at 9:00 AM
    start_time = datetime.strptime('9:00', '%H:%M')
    current_time = start_time
    itinerary = []
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Define variables for meeting order (0-3 representing the 4 friends)
    friend_names = list(friends.keys())
    problem.addVariables(['order_0', 'order_1', 'order_2', 'order_3'], range(4))
    problem.addConstraint(constraint.AllDifferentConstraint(), ['order_0', 'order_1', 'order_2', 'order_3'])
    
    # Find valid meeting sequences
    solutions = problem.getSolutions()
    
    best_solution = None
    max_meetings = 0
    
    for solution in solutions:
        order = [solution[f'order_{i}'] for i in range(4)]
        
        # Try to schedule meetings in this order
        current_location = 'Union Square'
        current_time = start_time
        scheduled_meetings = []
        meetings_count = 0
        
        for friend_idx in order:
            friend_name = friend_names[friend_idx]
            friend = friends[friend_name]
            location = friend['location']
            
            # Calculate travel time
            travel_time = travel_times.get((current_location, location), 60)  # Default to 60 if not found
            
            # Arrival time at friend's location
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            # Check if we can meet this friend
            if arrival_time < friend['available_end']:
                # Start meeting at the later of arrival time or friend's available start
                meeting_start = max(arrival_time, friend['available_start'])
                meeting_end = meeting_start + timedelta(minutes=friend['min_duration'])
                
                # Check if meeting fits within friend's availability
                if meeting_end <= friend['available_end']:
                    scheduled_meetings.append({
                        'friend': friend_name,
                        'location': location,
                        'start': meeting_start,
                        'end': meeting_end
                    })
                    meetings_count += 1
                    current_location = location
                    current_time = meeting_end
        
        # Update best solution if this one has more meetings
        if meetings_count > max_meetings:
            max_meetings = meetings_count
            best_solution = scheduled_meetings
    
    # Convert best solution to output format
    output_itinerary = []
    if best_solution:
        for meeting in best_solution:
            output_itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['friend'],
                "start_time": meeting['start'].strftime('%H:%M'),
                "end_time": meeting['end'].strftime('%H:%M')
            })
    
    # Output as JSON
    result = {
        "itinerary": output_itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()