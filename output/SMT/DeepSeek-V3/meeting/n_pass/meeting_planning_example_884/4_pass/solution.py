from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Bayview'): 27,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Bayview'): 20,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Bayview'): 22,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Bayview'): 16,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Bayview'): 19,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Bayview'): 25,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Bayview'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Bayview'): 31,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Golden Gate Park'): 22,
    }

    # Friends' availability and meeting constraints
    friends = {
        'Robert': {'location': 'Chinatown', 'start': 7*60 + 45, 'end': 17*60 + 30, 'duration': 120},
        'David': {'location': 'Sunset District', 'start': 12*60 + 30, 'end': 19*60 + 45, 'duration': 45},
        'Matthew': {'location': 'Alamo Square', 'start': 8*60 + 45, 'end': 13*60 + 45, 'duration': 90},
        'Jessica': {'location': 'Financial District', 'start': 9*60 + 30, 'end': 18*60 + 45, 'duration': 45},
        'Melissa': {'location': 'North Beach', 'start': 7*60 + 15, 'end': 16*60 + 45, 'duration': 45},
        'Mark': {'location': 'Embarcadero', 'start': 15*60 + 15, 'end': 17*60 + 0, 'duration': 45},
        'Deborah': {'location': 'Presidio', 'start': 19*60 + 0, 'end': 19*60 + 45, 'duration': 45},
        'Karen': {'location': 'Golden Gate Park', 'start': 19*60 + 30, 'end': 22*60 + 0, 'duration': 120},
        'Laura': {'location': 'Bayview', 'start': 21*60 + 15, 'end': 22*60 + 15, 'duration': 15},
    }

    # Current location and start time
    current_location = 'Richmond District'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Create variables for each friend's meeting
    meetings = []
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        location = friends[name]['location']
        duration = friends[name]['duration']
        available_start = friends[name]['start']
        available_end = friends[name]['end']
        
        # Add constraints for meeting time window
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + duration)
        s.add(start >= current_time)  # Can't start before arrival
        
        meetings.append({
            'name': name,
            'start': start,
            'end': end,
            'location': location
        })

    # Create a meeting order (sequence of meetings)
    num_meetings = len(meetings)
    order = [Int(f'order_{i}') for i in range(num_meetings)]
    
    # Each order position must be a unique meeting index
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 0)
        s.add(o < num_meetings)

    # Function to get travel time between two meetings
    def get_travel_time(meeting1, meeting2):
        return travel_times.get((meeting1['location'], meeting2['location']), 0)

    # Add constraints for travel times between consecutive meetings
    for i in range(num_meetings - 1):
        current_idx = order[i]
        next_idx = order[i + 1]
        
        # Get the corresponding meetings
        current_meeting = meetings[current_idx]
        next_meeting = meetings[next_idx]
        
        # Ensure enough time for travel
        s.add(next_meeting['start'] >= current_meeting['end'] + 
              get_travel_time(current_meeting, next_meeting))

    # First meeting must be reachable from starting location
    first_idx = order[0]
    first_meeting = meetings[first_idx]
    s.add(first_meeting['start'] >= current_time + 
          travel_times.get((current_location, first_meeting['location']), 0))

    # We want to maximize the number of meetings
    # Create a variable for each meeting indicating if it's selected
    selected = [Bool(f'selected_{name}') for name in friends]
    for i, name in enumerate(friends):
        s.add(selected[i] == Or([order[j] == i for j in range(num_meetings)]))

    # Maximize the number of selected meetings
    optimize = Optimize()
    for c in s.assertions():
        optimize.add(c)
    optimize.maximize(Sum([If(s, 1, 0) for s in selected]))

    if optimize.check() == sat:
        model = optimize.model()
        # Get the order of meetings
        meeting_order = [model[o].as_long() for o in order]
        
        # Collect all scheduled meetings in order
        scheduled_meetings = []
        for idx in meeting_order:
            meeting = meetings[idx]
            if model.evaluate(selected[idx]):
                start = model[meeting['start']].as_long()
                end = model[meeting['end']].as_long()
                scheduled_meetings.append({
                    'name': meeting['name'],
                    'start': start,
                    'end': end
                })
        
        # Build itinerary
        itinerary = []
        for meeting in scheduled_meetings:
            start_h = meeting['start'] // 60
            start_m = meeting['start'] % 60
            end_h = meeting['end'] // 60
            end_m = meeting['end'] % 60
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))