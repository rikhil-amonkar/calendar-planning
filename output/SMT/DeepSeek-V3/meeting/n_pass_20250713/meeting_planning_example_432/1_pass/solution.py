from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
    locations = ['GoldenGatePark', 'FishermansWharf', 'Bayview', 'MissionDistrict', 'Embarcadero', 'FinancialDistrict']
    friends = {
        'Joseph': {'location': 'FishermansWharf', 'available_start': 8*60, 'available_end': 17.5*60, 'duration': 90},
        'Jeffrey': {'location': 'Bayview', 'available_start': 17.5*60, 'available_end': 21.5*60, 'duration': 60},
        'Kevin': {'location': 'MissionDistrict', 'available_start': 11.25*60, 'available_end': 15.25*60, 'duration': 30},
        'David': {'location': 'Embarcadero', 'available_start': 8.25*60, 'available_end': 9*60, 'duration': 30},
        'Barbara': {'location': 'FinancialDistrict', 'available_start': 10.5*60, 'available_end': 16.5*60, 'duration': 15}
    }

    # Travel times dictionary (in minutes)
    travel_times = {
        ('GoldenGatePark', 'FishermansWharf'): 24,
        ('GoldenGatePark', 'Bayview'): 23,
        ('GoldenGatePark', 'MissionDistrict'): 17,
        ('GoldenGatePark', 'Embarcadero'): 25,
        ('GoldenGatePark', 'FinancialDistrict'): 26,
        ('FishermansWharf', 'GoldenGatePark'): 25,
        ('FishermansWharf', 'Bayview'): 26,
        ('FishermansWharf', 'MissionDistrict'): 22,
        ('FishermansWharf', 'Embarcadero'): 8,
        ('FishermansWharf', 'FinancialDistrict'): 11,
        ('Bayview', 'GoldenGatePark'): 22,
        ('Bayview', 'FishermansWharf'): 25,
        ('Bayview', 'MissionDistrict'): 13,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'FinancialDistrict'): 19,
        ('MissionDistrict', 'GoldenGatePark'): 17,
        ('MissionDistrict', 'FishermansWharf'): 22,
        ('MissionDistrict', 'Bayview'): 15,
        ('MissionDistrict', 'Embarcadero'): 19,
        ('MissionDistrict', 'FinancialDistrict'): 17,
        ('Embarcadero', 'GoldenGatePark'): 25,
        ('Embarcadero', 'FishermansWharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'MissionDistrict'): 20,
        ('Embarcadero', 'FinancialDistrict'): 5,
        ('FinancialDistrict', 'GoldenGatePark'): 23,
        ('FinancialDistrict', 'FishermansWharf'): 10,
        ('FinancialDistrict', 'Bayview'): 19,
        ('FinancialDistrict', 'MissionDistrict'): 17,
        ('FinancialDistrict', 'Embarcadero'): 4
    }

    # Variables for each friend's meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'GoldenGatePark'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        s.add(meeting_start[name] >= friend['available_start'])
        s.add(meeting_end[name] <= friend['available_end'])
        s.add(meeting_end[name] == meeting_start[name] + friend['duration'])

    # Order of meetings and travel times
    # We need to decide the order of meetings. For simplicity, we'll try to meet David first (since he's available earliest).
    # Then Barbara, Kevin, Joseph, and Jeffrey.
    # This is a heuristic; in practice, you might need to try different orders or use a more sophisticated approach.

    # Meet David at Embarcadero
    s.add(meeting_start['David'] >= current_time + travel_times[(current_location, 'Embarcadero')])
    current_time = meeting_end['David']
    current_location = 'Embarcadero'

    # Meet Barbara at Financial District
    s.add(meeting_start['Barbara'] >= current_time + travel_times[(current_location, 'FinancialDistrict')])
    current_time = meeting_end['Barbara']
    current_location = 'FinancialDistrict'

    # Meet Kevin at Mission District
    s.add(meeting_start['Kevin'] >= current_time + travel_times[(current_location, 'MissionDistrict')])
    current_time = meeting_end['Kevin']
    current_location = 'MissionDistrict'

    # Meet Joseph at Fisherman's Wharf
    s.add(meeting_start['Joseph'] >= current_time + travel_times[(current_location, 'FishermansWharf')])
    current_time = meeting_end['Joseph']
    current_location = 'FishermansWharf'

    # Meet Jeffrey at Bayview
    s.add(meeting_start['Jeffrey'] >= current_time + travel_times[(current_location, 'Bayview')])
    current_time = meeting_end['Jeffrey']
    current_location = 'Bayview'

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in friends:
            start = m[meeting_start[name]].as_long()
            end = m[meeting_end[name]].as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()