import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Financial District'): 17,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Financial District'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Embarcadero'): 4
    }

    # Friend constraints
    friends = {
        'Joseph': {
            'location': 'Fisherman\'s Wharf',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('17:30', '%H:%M'),
            'min_duration': 90
        },
        'Jeffrey': {
            'location': 'Bayview',
            'available_start': datetime.strptime('17:30', '%H:%M'),
            'available_end': datetime.strptime('21:30', '%H:%M'),
            'min_duration': 60
        },
        'Kevin': {
            'location': 'Mission District',
            'available_start': datetime.strptime('11:15', '%H:%M'),
            'available_end': datetime.strptime('15:15', '%H:%M'),
            'min_duration': 30
        },
        'David': {
            'location': 'Embarcadero',
            'available_start': datetime.strptime('8:15', '%H:%M'),
            'available_end': datetime.strptime('9:00', '%H:%M'),
            'min_duration': 30
        },
        'Barbara': {
            'location': 'Financial District',
            'available_start': datetime.strptime('10:30', '%H:%M'),
            'available_end': datetime.strptime('16:30', '%H:%M'),
            'min_duration': 15
        }
    }

    # Start at Golden Gate Park at 9:00
    start_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Golden Gate Park'

    problem = constraint.Problem()

    # Define variables for each friend: whether to meet them (0 or 1)
    for friend in friends:
        problem.addVariable(f'met_{friend}', [0, 1])

    # Define variables for meeting start times (in minutes from start of day)
    for friend in friends:
        friend_data = friends[friend]
        available_start_minutes = (friend_data['available_start'].hour * 60 + 
                                 friend_data['available_start'].minute)
        available_end_minutes = (friend_data['available_end'].hour * 60 + 
                               friend_data['available_end'].minute)
        
        # Generate possible start times within availability window
        possible_start_times = []
        for start_min in range(available_start_minutes, 
                             available_end_minutes - friend_data['min_duration'] + 1, 5):
            possible_start_times.append(start_min)
        
        problem.addVariable(f'start_{friend}', possible_start_times)

    # Constraint: Can only meet friends if we decide to meet them
    for friend in friends:
        problem.addConstraint(
            lambda met, start, friend=friend: (met == 1 and start is not None) or (met == 0 and start is None),
            [f'met_{friend}', f'start_{friend}']
        )

    # Constraint: Meetings must not overlap and must account for travel time
    def no_overlap_constraint(*args):
        # Extract meeting decisions and start times
        meeting_data = []
        for i, friend in enumerate(friends):
            met = args[i]
            start_min = args[i + len(friends)]
            if met == 1 and start_min is not None:
                friend_data = friends[friend]
                end_min = start_min + friend_data['min_duration']
                meeting_data.append({
                    'friend': friend,
                    'location': friend_data['location'],
                    'start': start_min,
                    'end': end_min
                })
        
        # Sort meetings by start time
        meeting_data.sort(key=lambda x: x['start'])
        
        # Check for overlaps and travel time constraints
        for i in range(len(meeting_data) - 1):
            current = meeting_data[i]
            next_meeting = meeting_data[i + 1]
            
            # Calculate travel time between locations
            travel_time = travel_times.get(
                (current['location'], next_meeting['location']), 0
            )
            
            # Check if there's enough time to travel between meetings
            if current['end'] + travel_time > next_meeting['start']:
                return False
        
        return True

    # Apply the no-overlap constraint
    all_vars = [f'met_{friend}' for friend in friends] + [f'start_{friend}' for friend in friends]
    problem.addConstraint(no_overlap_constraint, all_vars)

    # Constraint: First meeting must be reachable from starting location
    def first_meeting_constraint(*args):
        meeting_data = []
        for i, friend in enumerate(friends):
            met = args[i]
            start_min = args[i + len(friends)]
            if met == 1 and start_min is not None:
                meeting_data.append({
                    'friend': friend,
                    'location': friends[friend]['location'],
                    'start': start_min
                })
        
        if not meeting_data:
            return True
        
        # Find earliest meeting
        earliest_meeting = min(meeting_data, key=lambda x: x['start'])
        
        # Check if we can reach the first meeting from starting location
        travel_time = travel_times.get(
            (current_location, earliest_meeting['location']), 0
        )
        
        start_time_minutes = start_time.hour * 60 + start_time.minute
        return earliest_meeting['start'] >= start_time_minutes + travel_time

    problem.addConstraint(first_meeting_constraint, all_vars)

    # Objective: Maximize number of friends met
    def objective_function(*args):
        # Count number of friends met
        met_count = 0
        for i, friend in enumerate(friends):
            if args[i] == 1:
                met_count += 1
        return met_count

    # Find solutions and pick the one with maximum meetings
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet at least some friends
        best_solution = {}
        for friend in friends:
            best_solution[f'met_{friend}'] = 0
            best_solution[f'start_{friend}'] = None
    else:
        best_solution = max(solutions, key=lambda sol: objective_function(*[sol[f'met_{friend}'] for friend in friends]))

    # Build itinerary
    itinerary = []
    
    # Add meetings that are scheduled
    meeting_events = []
    for friend in friends:
        if best_solution[f'met_{friend}'] == 1 and best_solution[f'start_{friend}'] is not None:
            start_min = best_solution[f'start_{friend}']
            duration = friends[friend]['min_duration']
            end_min = start_min + duration
            
            start_time_obj = datetime(2023, 1, 1, start_min // 60, start_min % 60)
            end_time_obj = datetime(2023, 1, 1, end_min // 60, end_min % 60)
            
            meeting_events.append({
                'action': 'meet',
                'location': friends[friend]['location'],
                'person': friend,
                'start_time': start_time_obj.strftime('%H:%M'),
                'end_time': end_time_obj.strftime('%H:%M'),
                'start_minutes': start_min
            })
    
    # Sort meetings by start time
    meeting_events.sort(key=lambda x: x['start_minutes'])
    
    # Add travel events and build final itinerary
    current_time = start_time
    current_loc = current_location
    
    for i, meeting in enumerate(meeting_events):
        # Add travel time if needed
        if current_loc != meeting['location']:
            travel_time = travel_times.get((current_loc, meeting['location']), 0)
            travel_end = current_time + timedelta(minutes=travel_time)
            
            # Ensure we don't arrive before meeting starts
            meeting_start = datetime.strptime(meeting['start_time'], '%H:%M')
            if travel_end > meeting_start:
                # Adjust meeting start time if we arrive late
                meeting['start_time'] = travel_end.strftime('%H:%M')
                meeting_end = travel_end + timedelta(minutes=friends[meeting['person']]['min_duration'])
                meeting['end_time'] = meeting_end.strftime('%H:%M')
            
            current_time = travel_end
        
        # Add meeting to itinerary
        itinerary.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': meeting['start_time'],
            'end_time': meeting['end_time']
        })
        
        # Update current time and location
        current_time = datetime.strptime(meeting['end_time'], '%H:%M')
        current_loc = meeting['location']

    # Output result as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()