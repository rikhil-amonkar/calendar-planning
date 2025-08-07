from z3 import *
import json
from itertools import permutations

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define locations and travel times
    locations = ['Financial District', 'Chinatown', 'Alamo Square', 'Bayview', 'Fisherman\'s Wharf']
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
    }

    # Define friends and their constraints
    friends = {
        'Nancy': {
            'location': 'Chinatown',
            'available_start': 9.5,   # 9:30 AM
            'available_end': 13.5,    # 1:30 PM
            'min_duration': 1.5       # 90 minutes
        },
        'Mary': {
            'location': 'Alamo Square',
            'available_start': 7.0,   # 7:00 AM
            'available_end': 21.0,    # 9:00 PM
            'min_duration': 1.25      # 75 minutes
        },
        'Jessica': {
            'location': 'Bayview',
            'available_start': 11.25, # 11:15 AM
            'available_end': 13.75,   # 1:45 PM
            'min_duration': 0.75      # 45 minutes
        },
        'Rebecca': {
            'location': 'Fisherman\'s Wharf',
            'available_start': 7.0,   # 7:00 AM
            'available_end': 8.5,     # 8:30 AM
            'min_duration': 0.75      # 45 minutes
        }
    }

    # Current time starts at 9:00 AM in Financial District
    current_time = 9.0
    current_location = 'Financial District'

    # Variables for each meeting
    meetings = {}
    for friend in friends:
        meetings[friend] = {
            'start': Real(f'{friend}_start'),
            'end': Real(f'{friend}_end'),
            'met': Bool(f'{friend}_met')
        }

    # Constraints for each friend
    for friend in friends:
        data = friends[friend]
        start = meetings[friend]['start']
        end = meetings[friend]['end']
        met = meetings[friend]['met']

        # If met, then the meeting must be within availability and meet duration
        s.add(Implies(met, start >= data['available_start']))
        s.add(Implies(met, end <= data['available_end']))
        s.add(Implies(met, end == start + data['min_duration']))

        # If not met, then start and end are unconstrained
        s.add(Implies(Not(met), start == -1))
        s.add(Implies(Not(met), end == -1))

    # Create variables for travel times between meetings
    # We'll model the sequence of meetings explicitly
    # Since there are only 4 friends, we can enumerate all possible orders
    meeting_orders = list(permutations(friends.keys()))
    
    # Create a variable to indicate which meeting order is selected
    order_vars = [Bool(f'order_{i}') for i in range(len(meeting_orders))]
    s.add(Sum([If(var, 1, 0) for var in order_vars]) == 1)  # Exactly one order is selected

    # For each possible order, add constraints
    for i, order in enumerate(meeting_orders):
        prev_time = current_time
        prev_loc = current_location
        travel_constraints = []
        
        for j, friend in enumerate(order):
            met = meetings[friend]['met']
            start = meetings[friend]['start']
            end = meetings[friend]['end']
            loc = friends[friend]['location']
            
            # Create all possible travel time constraints for this step
            for from_loc in locations:
                for to_loc in locations:
                    if (from_loc, to_loc) in travel_times:
                        travel_time = travel_times[(from_loc, to_loc)]
                        # If previous location was from_loc and we're going to to_loc
                        travel_constraints.append(
                            Implies(
                                And(order_vars[i], met, prev_loc == from_loc, loc == to_loc),
                                start >= prev_time + travel_time
                            )
                        )
            
            # Update previous time and location if meeting happened
            prev_time = If(And(order_vars[i], met), end, prev_time)
            prev_loc = If(And(order_vars[i], met), loc, prev_loc)
        
        # Add all travel constraints for this order
        s.add(Implies(order_vars[i], And(*travel_constraints)))

    # Maximize the number of friends met
    total_met = Sum([If(meetings[friend]['met'], 1, 0) for friend in friends])
    s.maximize(total_met)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            if is_true(m[meetings[friend]['met']]):
                start = m[meetings[friend]['start']].as_fraction()
                end = m[meetings[friend]['end']].as_fraction()
                # Convert fractional hours to HH:MM format
                start_hour = int(float(start))
                start_minute = int((float(start) - start_hour) * 60)
                end_hour = int(float(end))
                end_minute = int((float(end) - end_hour) * 60)
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))