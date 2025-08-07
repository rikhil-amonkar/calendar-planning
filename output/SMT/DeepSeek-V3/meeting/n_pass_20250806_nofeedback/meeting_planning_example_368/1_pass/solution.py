from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the travel times as a dictionary for easy lookup
    travel_times = {
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Financial District'): 19,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Financial District'): 11,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
    }

    # Define friends' availability and meeting durations
    friends = {
        'Joseph': {
            'location': 'Russian Hill',
            'start_available': '8:30',
            'end_available': '19:15',
            'min_duration': 60,
        },
        'Nancy': {
            'location': 'Alamo Square',
            'start_available': '11:00',
            'end_available': '16:00',
            'min_duration': 90,
        },
        'Jason': {
            'location': 'North Beach',
            'start_available': '16:45',
            'end_available': '21:45',
            'min_duration': 15,
        },
        'Jeffrey': {
            'location': 'Financial District',
            'start_available': '10:30',
            'end_available': '15:45',
            'min_duration': 45,
        }
    }

    # Convert time strings to minutes since midnight for easier handling
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Bayview at 9:00 AM (540 minutes)
    current_location = 'Bayview'
    current_time = time_to_minutes('9:00')

    itinerary = []

    # We'll try to schedule meetings in a feasible order. Let's try Joseph, Jeffrey, Nancy, Jason.
    # This is one possible order; if it fails, we can try others.
    # But for this problem, let's assume this order works.

    # Schedule Joseph
    joseph = friends['Joseph']
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    travel_to_joseph = travel_times[(current_location, joseph['location'])]
    s.add(joseph_start >= current_time + travel_to_joseph)
    s.add(joseph_end == joseph_start + joseph['min_duration'])
    s.add(joseph_start >= time_to_minutes(joseph['start_available']))
    s.add(joseph_end <= time_to_minutes(joseph['end_available']))
    current_location = joseph['location']
    current_time = joseph_end

    # Schedule Jeffrey
    jeffrey = friends['Jeffrey']
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    travel_to_jeffrey = travel_times[(current_location, jeffrey['location'])]
    s.add(jeffrey_start >= current_time + travel_to_jeffrey)
    s.add(jeffrey_end == jeffrey_start + jeffrey['min_duration'])
    s.add(jeffrey_start >= time_to_minutes(jeffrey['start_available']))
    s.add(jeffrey_end <= time_to_minutes(jeffrey['end_available']))
    current_location = jeffrey['location']
    current_time = jeffrey_end

    # Schedule Nancy
    nancy = friends['Nancy']
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    travel_to_nancy = travel_times[(current_location, nancy['location'])]
    s.add(nancy_start >= current_time + travel_to_nancy)
    s.add(nancy_end == nancy_start + nancy['min_duration'])
    s.add(nancy_start >= time_to_minutes(nancy['start_available']))
    s.add(nancy_end <= time_to_minutes(nancy['end_available']))
    current_location = nancy['location']
    current_time = nancy_end

    # Schedule Jason
    jason = friends['Jason']
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    travel_to_jason = travel_times[(current_location, jason['location'])]
    s.add(jason_start >= current_time + travel_to_jason)
    s.add(jason_end == jason_start + jason['min_duration'])
    s.add(jason_start >= time_to_minutes(jason['start_available']))
    s.add(jason_end <= time_to_minutes(jason['end_available']))

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        joseph_start_val = model.eval(joseph_start).as_long()
        joseph_end_val = model.eval(joseph_end).as_long()
        jeffrey_start_val = model.eval(jeffrey_start).as_long()
        jeffrey_end_val = model.eval(jeffrey_end).as_long()
        nancy_start_val = model.eval(nancy_start).as_long()
        nancy_end_val = model.eval(nancy_end).as_long()
        jason_start_val = model.eval(jason_start).as_long()
        jason_end_val = model.eval(jason_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Joseph", "start_time": minutes_to_time(joseph_start_val), "end_time": minutes_to_time(joseph_end_val)},
            {"action": "meet", "person": "Jeffrey", "start_time": minutes_to_time(jeffrey_start_val), "end_time": minutes_to_time(jeffrey_end_val)},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(nancy_start_val), "end_time": minutes_to_time(nancy_end_val)},
            {"action": "meet", "person": "Jason", "start_time": minutes_to_time(jason_start_val), "end_time": minutes_to_time(jason_end_val)},
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver and print the result
result = solve_scheduling()
print(result)