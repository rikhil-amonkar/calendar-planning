from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes) between locations
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
        ('Embarcadero', 'Marina District'): 12,
    }

    # Define friends' availability and meeting constraints
    friends = {
        'Thomas': {
            'location': 'Bayview',
            'start': 15 * 60 + 30,  # 15:30 in minutes
            'end': 18 * 60 + 30,    # 18:30 in minutes
            'duration': 120          # 120 minutes
        },
        'Stephanie': {
            'location': 'Golden Gate Park',
            'start': 18 * 60 + 30,   # 18:30 in minutes
            'end': 21 * 60 + 45,     # 21:45 in minutes
            'duration': 30           # 30 minutes
        },
        'Laura': {
            'location': 'Nob Hill',
            'start': 8 * 60 + 45,   # 8:45 in minutes
            'end': 16 * 60 + 15,    # 16:15 in minutes
            'duration': 30          # 30 minutes
        },
        'Betty': {
            'location': 'Marina District',
            'start': 18 * 60 + 45,   # 18:45 in minutes
            'end': 21 * 60 + 45,     # 21:45 in minutes
            'duration': 45           # 45 minutes
        },
        'Patricia': {
            'location': 'Embarcadero',
            'start': 17 * 60 + 30,   # 17:30 in minutes
            'end': 22 * 60 + 0,      # 22:00 in minutes
            'duration': 45           # 45 minutes
        }
    }

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for friend in friends:
        meeting_vars[friend] = {
            'start': Int(f'start_{friend}'),
            'end': Int(f'end_{friend}')
        }

    # Add constraints for each meeting
    for friend in friends:
        info = friends[friend]
        start = meeting_vars[friend]['start']
        end = meeting_vars[friend]['end']
        s.add(start >= info['start'])
        s.add(end <= info['end'])
        s.add(end == start + info['duration'])

    # Initial location is Fisherman's Wharf at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Fisherman\'s Wharf'

    # Order of meetings to try (this is a heuristic to help the solver)
    meeting_order = ['Laura', 'Thomas', 'Patricia', 'Betty', 'Stephanie']

    # Add travel time constraints between meetings
    for i in range(len(meeting_order)):
        friend = meeting_order[i]
        location = friends[friend]['location']
        # Travel time from current_location to friend's location
        travel_time = travel_times.get((current_location, location), 0)
        # Ensure the meeting starts after travel time
        s.add(meeting_vars[friend]['start'] >= current_time + travel_time)
        # Update current_time and current_location
        current_time = meeting_vars[friend]['end']
        current_location = location

    # Ensure no overlapping meetings (though our order should prevent this)
    for i in range(len(meeting_order)):
        for j in range(i + 1, len(meeting_order)):
            friend1 = meeting_order[i]
            friend2 = meeting_order[j]
            s.add(Or(
                meeting_vars[friend1]['end'] <= meeting_vars[friend2]['start'],
                meeting_vars[friend2]['end'] <= meeting_vars[friend1]['start']
            ))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in meeting_order:
            start = model[meeting_vars[friend]['start']].as_long()
            end = model[meeting_vars[friend]['end']].as_long()
            # Convert minutes to HH:MM format
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))