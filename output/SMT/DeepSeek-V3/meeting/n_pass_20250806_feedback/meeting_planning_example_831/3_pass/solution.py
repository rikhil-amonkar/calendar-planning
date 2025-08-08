from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Richmond District'): 7,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Sunset District'): 27,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Richmond District'): 11,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Sunset District'): 30,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Richmond District'): 21,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Sunset District'): 27,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Richmond District'): 20,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Fisherman\'s Wharf'): 29,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Richmond District'): 12,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Richmond District'): 21,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Richmond District'): 20,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Chinatown'): 20,
    }

    # Define friends' availability and constraints
    friends = {
        'Jeffrey': {
            'location': 'Fisherman\'s Wharf',
            'start': 10.25,  # 10:15 AM
            'end': 13.0,      # 1:00 PM
            'duration': 1.5   # 90 minutes
        },
        'Ronald': {
            'location': 'Alamo Square',
            'start': 7.75,     # 7:45 AM
            'end': 14.75,     # 2:45 PM
            'duration': 2.0    # 120 minutes
        },
        'Jason': {
            'location': 'Financial District',
            'start': 10.75,   # 10:45 AM
            'end': 16.0,      # 4:00 PM
            'duration': 1.75  # 105 minutes
        },
        'Melissa': {
            'location': 'Union Square',
            'start': 17.75,    # 5:45 PM
            'end': 18.25,      # 6:15 PM
            'duration': 0.25   # 15 minutes
        },
        'Elizabeth': {
            'location': 'Sunset District',
            'start': 14.75,   # 2:45 PM
            'end': 17.5,       # 5:30 PM
            'duration': 1.75   # 105 minutes
        },
        'Margaret': {
            'location': 'Embarcadero',
            'start': 13.25,    # 1:15 PM
            'end': 19.0,       # 7:00 PM
            'duration': 1.5     # 90 minutes
        },
        'George': {
            'location': 'Golden Gate Park',
            'start': 19.0,     # 7:00 PM
            'end': 22.0,       # 10:00 PM
            'duration': 1.25    # 75 minutes
        },
        'Richard': {
            'location': 'Chinatown',
            'start': 9.5,      # 9:30 AM
            'end': 21.0,       # 9:00 PM
            'duration': 0.25    # 15 minutes
        },
        'Laura': {
            'location': 'Richmond District',
            'start': 9.75,     # 9:45 AM
            'end': 18.0,       # 6:00 PM
            'duration': 1.0     # 60 minutes
        }
    }

    # Define variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Real(f'start_{name}'),
            'end': Real(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Current location starts at Presidio at 9:00 AM
    current_time = Real('current_time')
    opt.add(current_time == 9.0)
    current_location = 'Presidio'

    # Ensure each meeting is within the friend's availability
    for name in friends:
        friend = friends[name]
        start = meeting_vars[name]['start']
        end = meeting_vars[name]['end']
        met = meeting_vars[name]['met']

        # Meeting must start and end within friend's availability
        opt.add(Implies(met, start >= friend['start']))
        opt.add(Implies(met, end <= friend['end']))
        opt.add(Implies(met, end == start + friend['duration']))

    # Define the order of meetings (this is a simplification; in practice, you'd need to explore permutations)
    # Here, we prioritize meeting friends with tighter time windows first
    meeting_order = ['Richard', 'Laura', 'Jeffrey', 'Ronald', 'Jason', 'Elizabeth', 'Margaret', 'Melissa', 'George']

    # Ensure no overlapping meetings and account for travel times
    for i in range(len(meeting_order) - 1):
        name1 = meeting_order[i]
        name2 = meeting_order[i + 1]
        loc1 = friends[name1]['location']
        loc2 = friends[name2]['location']
        travel_time = travel_times[(loc1, loc2)] / 60.0  # Convert to hours

        # If both meetings are scheduled, ensure enough time to travel
        opt.add(Implies(And(meeting_vars[name1]['met'], meeting_vars[name2]['met']),
                      meeting_vars[name2]['start'] >= meeting_vars[name1]['end'] + travel_time))

    # Ensure the first meeting starts after traveling from Presidio
    first_meeting = meeting_order[0]
    first_loc = friends[first_meeting]['location']
    travel_time = travel_times[(current_location, first_loc)] / 60.0
    opt.add(Implies(meeting_vars[first_meeting]['met'],
                  meeting_vars[first_meeting]['start'] >= current_time + travel_time))

    # Maximize the number of friends met
    total_met = Sum([If(meeting_vars[name]['met'], 1, 0) for name in friends])
    opt.maximize(total_met)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in meeting_order:
            if is_true(m[meeting_vars[name]['met']]):
                start = m[meeting_vars[name]['start']].as_fraction()
                end = m[meeting_vars[name]['end']].as_fraction()
                start_time = float(start)
                end_time = float(end)
                # Convert to HH:MM format
                start_hh = int(start_time)
                start_mm = int((start_time - start_hh) * 60)
                end_hh = int(end_time)
                end_mm = int((end_time - end_hh) * 60)
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))