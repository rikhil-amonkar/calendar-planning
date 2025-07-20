from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Embarcadero'): 31,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Embarcadero'): 25,
    }

    # Friends' availability and constraints
    friends = {
        'Emily': {'location': 'Russian Hill', 'start': '12:15', 'end': '14:15', 'min_duration': 105},
        'Mark': {'location': 'Presidio', 'start': '14:45', 'end': '19:30', 'min_duration': 60},
        'Deborah': {'location': 'Chinatown', 'start': '07:30', 'end': '15:30', 'min_duration': 45},
        'Margaret': {'location': 'Sunset District', 'start': '21:30', 'end': '22:30', 'min_duration': 60},
        'George': {'location': 'The Castro', 'start': '07:30', 'end': '14:15', 'min_duration': 60},
        'Andrew': {'location': 'Embarcadero', 'start': '20:15', 'end': '22:00', 'min_duration': 75},
        'Steven': {'location': 'Golden Gate Park', 'start': '11:15', 'end': '21:15', 'min_duration': 105},
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {'start': start_var, 'end': end_var}

    # Current location starts at Alamo Square at 9:00 AM (540 minutes)
    current_location = 'Alamo Square'
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each friend's meeting
    for name, data in friends.items():
        start_min = time_to_minutes(data['start'])
        end_min = time_to_minutes(data['end'])
        min_duration = data['min_duration']

        s.add(meeting_vars[name]['start'] >= start_min)
        s.add(meeting_vars[name]['end'] <= end_min)
        s.add(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= min_duration)

    # Define the order of meetings as a permutation of friends
    friends_list = list(friends.keys())
    n = len(friends_list)
    order = [Int(f'order_{i}') for i in range(n)]
    s.add(Distinct(order))
    for i in range(n):
        s.add(And(order[i] >= 0, order[i] < n))

    # Constraints for travel times between meetings
    # We need to model the sequence properly without direct list access
    for i in range(n):
        for j in range(n):
            if i != j:
                # Create a boolean variable indicating if friend j comes immediately after friend i
                comes_after = Bool(f'comes_after_{i}_{j}')
                s.add(comes_after == (order[j] == order[i] + 1))
                
                # If friend j comes after friend i, add the travel time constraint
                s.add(Implies(comes_after,
                    And(
                        meeting_vars[friends_list[j]]['start'] >= meeting_vars[friends_list[i]]['end'] + 
                        travel_times[(friends[friends_list[i]]['location'], friends[friends_list[j]]['location'])]
                    )
                ))

    # Ensure the first meeting starts after arriving at the first friend's location
    # We need to find which friend is first in the order
    for i in range(n):
        is_first = Bool(f'is_first_{i}')
        s.add(is_first == (order[i] == 0))
        s.add(Implies(is_first,
            meeting_vars[friends_list[i]]['start'] >= current_time + 
            travel_times[(current_location, friends[friends_list[i]]['location'])]
        ))

    # Add all duration constraints
    duration_constraints = []
    for name in friends:
        duration_constraints.append(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friends[name]['min_duration'])
    s.add(And(duration_constraints))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Get the order of meetings
        meeting_order = sorted([(m.evaluate(order[i]).as_long(), friends_list[i]) for i in range(n)], key=lambda x: x[0])
        itinerary = []
        for _, name in meeting_order:
            start = m[meeting_vars[name]['start']].as_long()
            end = m[meeting_vars[name]['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))