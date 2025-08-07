from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times as a dictionary for easy lookup
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

    # Define friends and their availability
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

    # Initialize variables for each meeting
    meetings = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meetings[name] = {
            'start_var': start_var,
            'end_var': end_var,
            'location': friends[name]['location'],
            'min_duration': friends[name]['min_duration'],
            'available_start': time_to_minutes(friends[name]['start']),
            'available_end': time_to_minutes(friends[name]['end']),
        }

    # Add constraints for each meeting
    for name in meetings:
        m = meetings[name]
        s.add(m['start_var'] >= m['available_start'])
        s.add(m['end_var'] <= m['available_end'])
        s.add(m['end_var'] - m['start_var'] >= m['min_duration'])

    # Starting at Alamo Square at 9:00 AM (540 minutes)
    current_location = 'Alamo Square'
    current_time = 540  # 9:00 AM in minutes

    # Define the order of meetings as a permutation to explore
    friend_names = list(friends.keys())
    # Limit permutations to a manageable number (e.g., 100) for performance
    for order in permutations(friend_names, min(100, len(friend_names))):
        temp_solver = Solver()
        # Add all meeting constraints
        for name in meetings:
            m = meetings[name]
            temp_solver.add(m['start_var'] >= m['available_start'])
            temp_solver.add(m['end_var'] <= m['available_end'])
            temp_solver.add(m['end_var'] - m['start_var'] >= m['min_duration'])
        # Add travel constraints for this order
        prev_location = current_location
        prev_time = current_time
        for name in order:
            m = meetings[name]
            travel_time = travel_times.get((prev_location, m['location']), 0)
            temp_solver.add(m['start_var'] >= prev_time + travel_time)
            prev_location = m['location']
            prev_time = m['end_var']
        # Check if this order is feasible
        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            for name in order:
                start = model[meetings[name]['start_var']].as_long()
                end = model[meetings[name]['end_var']].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end),
                })
            return {"itinerary": itinerary}

    # If no feasible order found, return empty itinerary
    return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))