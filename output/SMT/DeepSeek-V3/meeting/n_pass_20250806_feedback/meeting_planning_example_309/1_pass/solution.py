from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

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
            'available_start': 9.5,  # 9:30 AM in hours
            'available_end': 13.5,   # 1:30 PM in hours
            'min_duration': 1.5      # 90 minutes in hours
        },
        'Mary': {
            'location': 'Alamo Square',
            'available_start': 7.0,  # 7:00 AM in hours
            'available_end': 21.0,    # 9:00 PM in hours
            'min_duration': 1.25      # 75 minutes in hours
        },
        'Jessica': {
            'location': 'Bayview',
            'available_start': 11.25, # 11:15 AM in hours
            'available_end': 13.75,   # 1:45 PM in hours
            'min_duration': 0.75     # 45 minutes in hours
        },
        'Rebecca': {
            'location': 'Fisherman\'s Wharf',
            'available_start': 7.0,   # 7:00 AM in hours
            'available_end': 8.5,     # 8:30 AM in hours
            'min_duration': 0.75      # 45 minutes in hours
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

        # If not met, then start and end are unconstrained (but we'll optimize to meet)
        s.add(Implies(Not(met), start == -1))
        s.add(Implies(Not(met), end == -1))

    # Constraints on meeting order and travel times
    # We need to decide the order of meetings and ensure travel times are respected
    # This is complex, so we'll use a simplified approach: try to meet Rebecca first if possible,
    # then Nancy, Jessica, and Mary in some order.

    # Try to meet Rebecca first (if possible)
    rebecca_met = meetings['Rebecca']['met']
    rebecca_start = meetings['Rebecca']['start']
    rebecca_end = meetings['Rebecca']['end']
    s.add(Implies(rebecca_met, rebecca_start >= current_time + travel_times[(current_location, friends['Rebecca']['location'])]))
    # After meeting Rebecca, update current time and location
    after_rebecca_time = If(rebecca_met, rebecca_end + travel_times[(friends['Rebecca']['location'], 'Financial District')], current_time)
    after_rebecca_location = If(rebecca_met, 'Financial District', current_location)

    # Then try to meet Nancy
    nancy_met = meetings['Nancy']['met']
    nancy_start = meetings['Nancy']['start']
    nancy_end = meetings['Nancy']['end']
    s.add(Implies(nancy_met, nancy_start >= after_rebecca_time + travel_times[(after_rebecca_location, friends['Nancy']['location'])]))
    after_nancy_time = If(nancy_met, nancy_end, after_rebecca_time)
    after_nancy_location = If(nancy_met, friends['Nancy']['location'], after_rebecca_location)

    # Then try to meet Jessica
    jessica_met = meetings['Jessica']['met']
    jessica_start = meetings['Jessica']['start']
    jessica_end = meetings['Jessica']['end']
    s.add(Implies(jessica_met, jessica_start >= after_nancy_time + travel_times[(after_nancy_location, friends['Jessica']['location'])]))
    after_jessica_time = If(jessica_met, jessica_end, after_nancy_time)
    after_jessica_location = If(jessica_met, friends['Jessica']['location'], after_nancy_location)

    # Finally try to meet Mary
    mary_met = meetings['Mary']['met']
    mary_start = meetings['Mary']['start']
    mary_end = meetings['Mary']['end']
    s.add(Implies(mary_met, mary_start >= after_jessica_time + travel_times[(after_jessica_location, friends['Mary']['location'])]))
    after_mary_time = If(mary_met, mary_end, after_jessica_time)
    after_mary_location = If(mary_met, friends['Mary']['location'], after_jessica_location)

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