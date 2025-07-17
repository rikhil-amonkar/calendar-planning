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

    # We'll model the schedule as a sequence of meetings
    # Create variables for each possible meeting slot
    max_meetings = len(friends)
    meeting_slots = []
    
    for i in range(max_meetings):
        slot = {
            'name': Int(f'slot_{i}_name'),
            'start': Int(f'slot_{i}_start'),
            'end': Int(f'slot_{i}_end'),
            'location': Int(f'slot_{i}_location'),
            'used': Bool(f'slot_{i}_used')
        }
        meeting_slots.append(slot)

    # Create mapping between names and locations
    name_to_id = {name: i for i, name in enumerate(friends)}
    location_to_id = {loc: i for i, loc in enumerate(set(f['location'] for f in friends.values()))}
    id_to_location = {i: loc for loc, i in location_to_id.items()}

    # Constraints for each slot
    for i in range(max_meetings):
        slot = meeting_slots[i]
        
        # If slot is used, it must be a valid meeting
        for name, info in friends.items():
            s.add(Implies(
                And(slot['used'], slot['name'] == name_to_id[name]),
                And(
                    slot['start'] >= info['start'],
                    slot['end'] <= info['end'],
                    slot['end'] == slot['start'] + info['duration'],
                    slot['location'] == location_to_id[info['location']]
                )
            ))
        
        # If slot is not used, set default values
        s.add(Implies(Not(slot['used']), 
                     And(slot['start'] == 0, slot['end'] == 0, slot['name'] == -1)))

    # Ordering constraints - each used slot must come after the previous one with travel time
    for i in range(max_meetings - 1):
        current_slot = meeting_slots[i]
        next_slot = meeting_slots[i + 1]
        
        # If both slots are used, ensure proper ordering with travel time
        s.add(Implies(
            And(current_slot['used'], next_slot['used']),
            next_slot['start'] >= current_slot['end'] + travel_times.get(
                (id_to_location[current_slot['location'].as_long()], 
                 id_to_location[next_slot['location'].as_long()]), 0)
        ))

    # First meeting must be reachable from starting location
    if max_meetings > 0:
        first_slot = meeting_slots[0]
        s.add(Implies(
            first_slot['used'],
            first_slot['start'] >= current_time + travel_times.get(
                (current_location, id_to_location[first_slot['location'].as_long()]), 0)
        ))

    # Each friend can be met at most once
    for name in friends:
        s.add(Sum([If(And(slot['used'], slot['name'] == name_to_id[name]), 1, 0) 
                  for slot in meeting_slots]) <= 1)

    # Maximize the number of meetings
    optimize = Optimize()
    for c in s.assertions():
        optimize.add(c)
    optimize.maximize(Sum([If(slot['used'], 1, 0) for slot in meeting_slots]))

    if optimize.check() == sat:
        model = optimize.model()
        # Collect all scheduled meetings
        scheduled_meetings = []
        for slot in meeting_slots:
            if model[slot['used']]:
                name = list(friends.keys())[model[slot['name']].as_long()]
                start = model[slot['start']].as_long()
                end = model[slot['end']].as_long()
                scheduled_meetings.append({
                    'name': name,
                    'start': start,
                    'end': end
                })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start'])
        
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