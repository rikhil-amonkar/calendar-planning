from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their locations, available times, and desired meeting durations
    friends = {
        'Matthew': {'location': 'Presidio', 'start': 8.25, 'end': 9.0, 'duration': 0.25},
        'Richard': {'location': 'Fisherman\'s Wharf', 'start': 11.0, 'end': 12.75, 'duration': 1.0},
        'Elizabeth': {'location': 'Nob Hill', 'start': 11.75, 'end': 18.5, 'duration': 1.25},
        'Anthony': {'location': 'Pacific Heights', 'start': 14.25, 'end': 16.0, 'duration': 0.5},
        'Brian': {'location': 'North Beach', 'start': 13.0, 'end': 19.0, 'duration': 1.5},
        'Kenneth': {'location': 'Chinatown', 'start': 13.75, 'end': 19.5, 'duration': 1.75},
        'Ashley': {'location': 'Haight-Ashbury', 'start': 15.0, 'end': 20.5, 'duration': 1.5},
        'Kimberly': {'location': 'Alamo Square', 'start': 17.5, 'end': 21.25, 'duration': 0.75},
        'Deborah': {'location': 'Union Square', 'start': 17.5, 'end': 22.0, 'duration': 1.0},
        'Jessica': {'location': 'Golden Gate Park', 'start': 20.0, 'end': 21.75, 'duration': 1.75}
    }

    # Travel times dictionary (simplified for brevity, but you can expand it as needed)
    travel_times = {
        ('Bayview', 'Presidio'): 32/60,
        ('Presidio', 'Fisherman\'s Wharf'): 19/60,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11/60,
        ('Nob Hill', 'Pacific Heights'): 8/60,
        ('Pacific Heights', 'North Beach'): 9/60,
        ('North Beach', 'Chinatown'): 6/60,
        ('Chinatown', 'Haight-Ashbury'): 19/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Alamo Square', 'Union Square'): 14/60,
        ('Union Square', 'Golden Gate Park'): 22/60
    }

    # Variables for arrival and departure times at each friend's location
    arrival = {name: Real(f'arrival_{name}') for name in friends}
    departure = {name: Real(f'departure_{name}') for name in friends}

    # Initial constraints: start at Bayview at 9:00 AM
    s.add(arrival['Matthew'] == 8.25)  # Meeting Matthew at Presidio at 8:15 AM is not possible since we arrive at Bayview at 9:00 AM
    # So, we skip Matthew and start from Bayview at 9:00 AM

    # We'll model the sequence of visits, ensuring travel times and meeting durations are respected
    # For simplicity, let's assume a fixed order (this can be optimized further)
    # Order: Bayview -> Fisherman's Wharf (Richard) -> Nob Hill (Elizabeth) -> Pacific Heights (Anthony) -> North Beach (Brian) -> Chinatown (Kenneth) -> Haight-Ashbury (Ashley) -> Alamo Square (Kimberly) -> Union Square (Deborah) -> Golden Gate Park (Jessica)

    # Constraints for each friend
    s.add(arrival['Richard'] >= 9.0 + travel_times[('Bayview', 'Fisherman\'s Wharf')])
    s.add(departure['Richard'] == arrival['Richard'] + friends['Richard']['duration'])
    s.add(arrival['Richard'] >= friends['Richard']['start'])
    s.add(departure['Richard'] <= friends['Richard']['end'])

    s.add(arrival['Elizabeth'] >= departure['Richard'] + travel_times[('Fisherman\'s Wharf', 'Nob Hill')])
    s.add(departure['Elizabeth'] == arrival['Elizabeth'] + friends['Elizabeth']['duration'])
    s.add(arrival['Elizabeth'] >= friends['Elizabeth']['start'])
    s.add(departure['Elizabeth'] <= friends['Elizabeth']['end'])

    s.add(arrival['Anthony'] >= departure['Elizabeth'] + travel_times[('Nob Hill', 'Pacific Heights')])
    s.add(departure['Anthony'] == arrival['Anthony'] + friends['Anthony']['duration'])
    s.add(arrival['Anthony'] >= friends['Anthony']['start'])
    s.add(departure['Anthony'] <= friends['Anthony']['end'])

    s.add(arrival['Brian'] >= departure['Anthony'] + travel_times[('Pacific Heights', 'North Beach')])
    s.add(departure['Brian'] == arrival['Brian'] + friends['Brian']['duration'])
    s.add(arrival['Brian'] >= friends['Brian']['start'])
    s.add(departure['Brian'] <= friends['Brian']['end'])

    s.add(arrival['Kenneth'] >= departure['Brian'] + travel_times[('North Beach', 'Chinatown')])
    s.add(departure['Kenneth'] == arrival['Kenneth'] + friends['Kenneth']['duration'])
    s.add(arrival['Kenneth'] >= friends['Kenneth']['start'])
    s.add(departure['Kenneth'] <= friends['Kenneth']['end'])

    s.add(arrival['Ashley'] >= departure['Kenneth'] + travel_times[('Chinatown', 'Haight-Ashbury')])
    s.add(departure['Ashley'] == arrival['Ashley'] + friends['Ashley']['duration'])
    s.add(arrival['Ashley'] >= friends['Ashley']['start'])
    s.add(departure['Ashley'] <= friends['Ashley']['end'])

    s.add(arrival['Kimberly'] >= departure['Ashley'] + travel_times[('Haight-Ashbury', 'Alamo Square')])
    s.add(departure['Kimberly'] == arrival['Kimberly'] + friends['Kimberly']['duration'])
    s.add(arrival['Kimberly'] >= friends['Kimberly']['start'])
    s.add(departure['Kimberly'] <= friends['Kimberly']['end'])

    s.add(arrival['Deborah'] >= departure['Kimberly'] + travel_times[('Alamo Square', 'Union Square')])
    s.add(departure['Deborah'] == arrival['Deborah'] + friends['Deborah']['duration'])
    s.add(arrival['Deborah'] >= friends['Deborah']['start'])
    s.add(departure['Deborah'] <= friends['Deborah']['end'])

    s.add(arrival['Jessica'] >= departure['Deborah'] + travel_times[('Union Square', 'Golden Gate Park')])
    s.add(departure['Jessica'] == arrival['Jessica'] + friends['Jessica']['duration'])
    s.add(arrival['Jessica'] >= friends['Jessica']['start'])
    s.add(departure['Jessica'] <= friends['Jessica']['end'])

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        for name in friends:
            print(f"{name}: Arrival at {m[arrival[name]]}, Departure at {m[departure[name]]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()