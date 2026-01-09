import constraint
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

    # Create problem
    problem = constraint.Problem()

    # Variables: for each friend, whether we meet them (0 or 1)
    friend_names = list(friends.keys())
    for friend in friend_names:
        problem.addVariable(f'met_{friend}', [0, 1])

    # Variables: start and end times for each meeting (in minutes from start of day)
    day_start = datetime.strptime('0:00', '%H:%M')
    
    for friend in friend_names:
        friend_data = friends[friend]
        start_min = int((friend_data['start'] - day_start).total_seconds() / 60)
        end_min = int((friend_data['end'] - day_start).total_seconds() / 60)
        min_duration = friend_data['min_duration']
        
        # If we meet this friend, the meeting must fit within their availability
        problem.addVariable(f'start_{friend}', range(start_min, end_min - min_duration + 1))
        problem.addVariable(f'end_{friend}', range(start_min + min_duration, end_min + 1))

    # Constraint: if we don't meet a friend, set their times to 0
    for friend in friend_names:
        def no_meeting_constraint(met, start, end, friend=friend):
            if met == 0:
                return start == 0 and end == 0
            else:
                return start > 0 and end > 0 and (end - start) >= friends[friend]['min_duration']
        
        problem.addConstraint(no_meeting_constraint, 
                            [f'met_{friend}', f'start_{friend}', f'end_{friend}'])

    # Constraint: meetings must be in chronological order with travel time
    # We'll try different permutations of meeting order
    from itertools import permutations
    
    best_solution = None
    max_meetings = 0
    
    # Try different meeting orders
    for meeting_order in permutations(friend_names):
        temp_problem = problem
        
        # Add constraints for the chosen order
        for i in range(len(meeting_order) - 1):
            friend1 = meeting_order[i]
            friend2 = meeting_order[i + 1]
            loc1 = friends[friend1]['location']
            loc2 = friends[friend2]['location']
            travel_time = travel_times.get((loc1, loc2), 999)
            
            def travel_constraint(met1, end1, met2, start2, travel=travel_time):
                if met1 == 0 or met2 == 0:
                    return True
                return start2 >= end1 + travel
            
            temp_problem.addConstraint(travel_constraint, 
                                    [f'met_{friend1}', f'end_{friend1}', 
                                     f'met_{friend2}', f'start_{friend2}'])
        
        # First meeting must be after travel from start location
        first_friend = meeting_order[0]
        first_loc = friends[first_friend]['location']
        travel_from_start = travel_times.get((start_location, first_loc), 999)
        
        def start_constraint(met, start, travel=travel_from_start):
            if met == 0:
                return True
            start_time_min = int((start_time - day_start).total_seconds() / 60)
            return start >= start_time_min + travel
        
        temp_problem.addConstraint(start_constraint, 
                                [f'met_{first_friend}', f'start_{first_friend}'])
        
        # Try to find a solution
        solutions = temp_problem.getSolutions()
        
        if solutions:
            for solution in solutions:
                # Count how many friends we meet
                meetings_count = sum(solution[f'met_{friend}'] for friend in friend_names)
                
                if meetings_count > max_meetings:
                    max_meetings = meetings_count
                    best_solution = solution.copy()
                    best_solution['meeting_order'] = meeting_order

    # Format the output
    if best_solution:
        itinerary = []
        
        # Sort meetings by start time
        meeting_times = []
        for friend in friend_names:
            if best_solution[f'met_{friend}'] == 1:
                start_min = best_solution[f'start_{friend}']
                end_min = best_solution[f'end_{friend}']
                meeting_times.append((friend, start_min, end_min))
        
        meeting_times.sort(key=lambda x: x[1])
        
        for friend, start_min, end_min in meeting_times:
            start_time_obj = day_start + timedelta(minutes=start_min)
            end_time_obj = day_start + timedelta(minutes=end_min)
            
            itinerary.append({
                "action": "meet",
                "location": friends[friend]['location'],
                "person": friend,
                "start_time": start_time_obj.strftime('%H:%M').lstrip('0'),
                "end_time": end_time_obj.strftime('%H:%M').lstrip('0')
            })
        
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()