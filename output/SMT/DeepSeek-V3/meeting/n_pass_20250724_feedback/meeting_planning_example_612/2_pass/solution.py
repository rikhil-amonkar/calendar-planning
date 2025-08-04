from z3 import *
import json

def solve_scheduling_problem():
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

    # Define friends and their constraints
    friends = {
        'Emily': {'location': 'Russian Hill', 'start': '12:15', 'end': '14:15', 'min_duration': 105},
        'Mark': {'location': 'Presidio', 'start': '14:45', 'end': '19:30', 'min_duration': 60},
        'Deborah': {'location': 'Chinatown', 'start': '07:30', 'end': '15:30', 'min_duration': 45},
        'Margaret': {'location': 'Sunset District', 'start': '21:30', 'end': '22:30', 'min_duration': 60},
        'George': {'location': 'The Castro', 'start': '07:30', 'end': '14:15', 'min_duration': 60},
        'Andrew': {'location': 'Embarcadero', 'start': '20:15', 'end': '22:00', 'min_duration': 75},
        'Steven': {'location': 'Golden Gate Park', 'start': '11:15', 'end': '21:15', 'min_duration': 105},
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = (minutes // 60) % 24
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each meeting
    meetings = {}
    for person in friends:
        start_var = Int(f'start_{person}')
        end_var = Int(f'end_{person}')
        meetings[person] = {
            'start_var': start_var,
            'end_var': end_var,
            'location': friends[person]['location'],
            'min_duration': friends[person]['min_duration'],
            'available_start': time_to_minutes(friends[person]['start']),
            'available_end': time_to_minutes(friends[person]['end']),
        }
        # Constrain meeting to be within friend's availability
        s.add(start_var >= meetings[person]['available_start'])
        s.add(end_var <= meetings[person]['available_end'])
        # Constrain meeting duration
        s.add(end_var - start_var >= meetings[person]['min_duration'])

    # Initial location is Alamo Square at 9:00 AM (540 minutes)
    initial_time = 540
    initial_location = 'Alamo Square'

    # Define the order of meetings (we'll try to meet all friends)
    meeting_order = list(friends.keys())

    # Add constraints for travel times between meetings
    for i in range(len(meeting_order)):
        if i == 0:
            # First meeting: travel from initial location to first friend's location
            first_person = meeting_order[i]
            first_location = meetings[first_person]['location']
            travel_time = travel_times[(initial_location, first_location)]
            s.add(meetings[first_person]['start_var'] >= initial_time + travel_time)
        else:
            # Subsequent meetings: travel from previous friend's location to current friend's location
            prev_person = meeting_order[i-1]
            current_person = meeting_order[i]
            prev_location = meetings[prev_person]['location']
            current_location = meetings[current_person]['location']
            travel_time = travel_times[(prev_location, current_location)]
            s.add(meetings[current_person]['start_var'] >= meetings[prev_person]['end_var'] + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for person in meeting_order:
            start = model[meetings[person]['start_var']].as_long()
            end = model[meetings[person]['end_var']].as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
            })
        return {"itinerary": itinerary}
    else:
        # If not feasible, try to meet a subset of friends
        # We'll prioritize friends with earlier availability
        prioritized_order = sorted(friends.keys(), key=lambda x: friends[x]['available_start'])
        for i in range(len(prioritized_order), 0, -1):
            s.reset()
            subset = prioritized_order[:i]
            for person in subset:
                start_var = Int(f'start_{person}')
                end_var = Int(f'end_{person}')
                meetings[person] = {
                    'start_var': start_var,
                    'end_var': end_var,
                    'location': friends[person]['location'],
                    'min_duration': friends[person]['min_duration'],
                    'available_start': time_to_minutes(friends[person]['start']),
                    'available_end': time_to_minutes(friends[person]['end']),
                }
                s.add(start_var >= meetings[person]['available_start'])
                s.add(end_var <= meetings[person]['available_end'])
                s.add(end_var - start_var >= meetings[person]['min_duration'])
            for j in range(len(subset)):
                if j == 0:
                    first_person = subset[j]
                    first_location = meetings[first_person]['location']
                    travel_time = travel_times[(initial_location, first_location)]
                    s.add(meetings[first_person]['start_var'] >= initial_time + travel_time)
                else:
                    prev_person = subset[j-1]
                    current_person = subset[j]
                    prev_location = meetings[prev_person]['location']
                    current_location = meetings[current_person]['location']
                    travel_time = travel_times[(prev_location, current_location)]
                    s.add(meetings[current_person]['start_var'] >= meetings[prev_person]['end_var'] + travel_time)
            if s.check() == sat:
                model = s.model()
                itinerary = []
                for person in subset:
                    start = model[meetings[person]['start_var']].as_long()
                    end = model[meetings[person]['end_var']].as_long()
                    itinerary.append({
                        "action": "meet",
                        "person": person,
                        "start_time": minutes_to_time(start),
                        "end_time": minutes_to_time(end),
                    })
                return {"itinerary": itinerary}
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))