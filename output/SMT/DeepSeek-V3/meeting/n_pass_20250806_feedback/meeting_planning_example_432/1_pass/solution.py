from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()

    # Define the meeting durations in minutes
    joseph_duration = 90
    jeffrey_duration = 60
    kevin_duration = 30
    david_duration = 30
    barbara_duration = 15

    # Define the travel times between locations (in minutes)
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
        ('Financial District', 'Embarcadero'): 4,
    }

    # Define the friends' availability windows in minutes since 9:00 AM
    availability = {
        'Joseph': (8*60 - 9*60, 17*60 + 30 - 9*60),  # 8:00 AM to 5:30 PM
        'Jeffrey': (17*60 + 30 - 9*60, 21*60 + 30 - 9*60),  # 5:30 PM to 9:30 PM
        'Kevin': (11*60 + 15 - 9*60, 15*60 + 15 - 9*60),  # 11:15 AM to 3:15 PM
        'David': (8*60 + 15 - 9*60, 9*60 - 9*60),  # 8:15 AM to 9:00 AM
        'Barbara': (10*60 + 30 - 9*60, 16*60 + 30 - 9*60),  # 10:30 AM to 4:30 PM
    }

    # Define the locations of each friend
    locations = {
        'Joseph': 'Fisherman\'s Wharf',
        'Jeffrey': 'Bayview',
        'Kevin': 'Mission District',
        'David': 'Embarcadero',
        'Barbara': 'Financial District',
    }

    # Define the order of meetings (we'll try to meet all friends)
    friends = ['David', 'Barbara', 'Kevin', 'Joseph', 'Jeffrey']

    # Create variables for start and end times of each meeting
    start_vars = {f: Int(f'start_{f}') for f in friends}
    end_vars = {f: Int(f'end_{f}') for f in friends}

    # Add constraints for each meeting
    for f in friends:
        # Meeting duration
        solver.add(end_vars[f] == start_vars[f] + {
            'Joseph': joseph_duration,
            'Jeffrey': jeffrey_duration,
            'Kevin': kevin_duration,
            'David': david_duration,
            'Barbara': barbara_duration,
        }[f])

        # Availability window
        solver.add(start_vars[f] >= availability[f][0])
        solver.add(end_vars[f] <= availability[f][1])

    # Add travel time constraints between consecutive meetings
    for i in range(len(friends) - 1):
        f1 = friends[i]
        f2 = friends[i + 1]
        loc1 = locations[f1]
        loc2 = locations[f2]
        travel_time = travel_times[(loc1, loc2)]
        solver.add(start_vars[f2] >= end_vars[f1] + travel_time)

    # Ensure meetings are in the correct order (David first, then Barbara, etc.)
    for i in range(len(friends) - 1):
        solver.add(start_vars[friends[i]] <= start_vars[friends[i + 1]])

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for f in friends:
            start = model.eval(start_vars[f]).as_long()
            end = model.eval(end_vars[f]).as_long()
            # Convert minutes since 9:00 AM to HH:MM format
            start_hour = 9 + start // 60
            start_minute = start % 60
            end_hour = 9 + end // 60
            end_minute = end % 60
            itinerary.append({
                "action": "meet",
                "person": f,
                "start_time": f"{start_hour:02d}:{start_minute:02d}",
                "end_time": f"{end_hour:02d}:{end_minute:02d}",
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))