from z3 import *

def solve_scheduling():
    # Create solver
    s = Solver()

    # Locations
    locations = ['Financial_District', 'Golden_Gate_Park', 'Chinatown', 'Union_Square', 
                 'Fishermans_Wharf', 'Pacific_Heights', 'North_Beach']
    
    # Friends and their constraints
    friends = {
        'Stephanie': {'location': 'Golden_Gate_Park', 'start': 11*60, 'end': 15*60, 'min_duration': 105},
        'Karen': {'location': 'Chinatown', 'start': 13*60 + 45, 'end': 16*60 + 30, 'min_duration': 15},
        'Brian': {'location': 'Union_Square', 'start': 15*60, 'end': 17*60 + 15, 'min_duration': 30},
        'Rebecca': {'location': 'Fishermans_Wharf', 'start': 8*60, 'end': 11*60 + 15, 'min_duration': 30},
        'Joseph': {'location': 'Pacific_Heights', 'start': 8*60 + 15, 'end': 9*60 + 30, 'min_duration': 60},
        'Steven': {'location': 'North_Beach', 'start': 14*60 + 30, 'end': 20*60 + 45, 'min_duration': 120}
    }

    # Travel times (in minutes) between locations
    travel_times = {
        ('Financial_District', 'Golden_Gate_Park'): 23,
        ('Financial_District', 'Chinatown'): 5,
        ('Financial_District', 'Union_Square'): 9,
        ('Financial_District', 'Fishermans_Wharf'): 10,
        ('Financial_District', 'Pacific_Heights'): 13,
        ('Financial_District', 'North_Beach'): 7,
        ('Golden_Gate_Park', 'Financial_District'): 26,
        ('Golden_Gate_Park', 'Chinatown'): 23,
        ('Golden_Gate_Park', 'Union_Square'): 22,
        ('Golden_Gate_Park', 'Fishermans_Wharf'): 24,
        ('Golden_Gate_Park', 'Pacific_Heights'): 16,
        ('Golden_Gate_Park', 'North_Beach'): 24,
        ('Chinatown', 'Financial_District'): 5,
        ('Chinatown', 'Golden_Gate_Park'): 23,
        ('Chinatown', 'Union_Square'): 7,
        ('Chinatown', 'Fishermans_Wharf'): 8,
        ('Chinatown', 'Pacific_Heights'): 10,
        ('Chinatown', 'North_Beach'): 3,
        ('Union_Square', 'Financial_District'): 9,
        ('Union_Square', 'Golden_Gate_Park'): 22,
        ('Union_Square', 'Chinatown'): 7,
        ('Union_Square', 'Fishermans_Wharf'): 15,
        ('Union_Square', 'Pacific_Heights'): 15,
        ('Union_Square', 'North_Beach'): 10,
        ('Fishermans_Wharf', 'Financial_District'): 11,
        ('Fishermans_Wharf', 'Golden_Gate_Park'): 25,
        ('Fishermans_Wharf', 'Chinatown'): 12,
        ('Fishermans_Wharf', 'Union_Square'): 13,
        ('Fishermans_Wharf', 'Pacific_Heights'): 12,
        ('Fishermans_Wharf', 'North_Beach'): 6,
        ('Pacific_Heights', 'Financial_District'): 13,
        ('Pacific_Heights', 'Golden_Gate_Park'): 15,
        ('Pacific_Heights', 'Chinatown'): 11,
        ('Pacific_Heights', 'Union_Square'): 12,
        ('Pacific_Heights', 'Fishermans_Wharf'): 13,
        ('Pacific_Heights', 'North_Beach'): 9,
        ('North_Beach', 'Financial_District'): 8,
        ('North_Beach', 'Golden_Gate_Park'): 22,
        ('North_Beach', 'Chinatown'): 6,
        ('North_Beach', 'Union_Square'): 7,
        ('North_Beach', 'Fishermans_Wharf'): 5,
        ('North_Beach', 'Pacific_Heights'): 8
    }

    # Variables for arrival and departure times at each location
    arrival = {loc: Int(f'arrival_{loc}') for loc in locations}
    departure = {loc: Int(f'departure_{loc}') for loc in locations}

    # Initial constraints: start at Financial District at 9:00 AM (540 minutes)
    s.add(arrival['Financial_District'] == 540)
    s.add(departure['Financial_District'] >= arrival['Financial_District'])

    # Variables to track if we meet each friend
    met = {friend: Bool(f'met_{friend}') for friend in friends}

    # Constraints for each friend
    for friend, data in friends.items():
        loc = data['location']
        start = data['start']
        end = data['end']
        min_duration = data['min_duration']

        # If we meet the friend, their constraints must be satisfied
        s.add(Implies(met[friend], 
                     And(arrival[loc] >= start,
                         departure[loc] <= end,
                         departure[loc] - arrival[loc] >= min_duration)))

        # If we don't meet the friend, no time spent at their location during their window
        s.add(Implies(Not(met[friend]),
                     Or(arrival[loc] > end,
                        departure[loc] < start)))

    # Define possible sequences that could meet 5 friends
    # We'll try excluding each friend one by one to find a feasible schedule
    
    # Try excluding Joseph first (since his window is early and short)
    s.push()
    s.add(Not(met['Joseph']))
    s.add(And([met[f] for f in friends if f != 'Joseph']))
    
    # Travel constraints for sequence: Financial -> Pacific -> Fishermans -> Golden Gate -> Chinatown -> North Beach -> Union Square
    s.add(arrival['Pacific_Heights'] >= departure['Financial_District'] + travel_times[('Financial_District', 'Pacific_Heights')])
    s.add(arrival['Fishermans_Wharf'] >= departure['Pacific_Heights'] + travel_times[('Pacific_Heights', 'Fishermans_Wharf')])
    s.add(arrival['Golden_Gate_Park'] >= departure['Fishermans_Wharf'] + travel_times[('Fishermans_Wharf', 'Golden_Gate_Park')])
    s.add(arrival['Chinatown'] >= departure['Golden_Gate_Park'] + travel_times[('Golden_Gate_Park', 'Chinatown')])
    s.add(arrival['North_Beach'] >= departure['Chinatown'] + travel_times[('Chinatown', 'North_Beach')])
    s.add(arrival['Union_Square'] >= departure['North_Beach'] + travel_times[('North_Beach', 'Union_Square')])

    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found (excluding Joseph)!")
        print("Meeting exactly 5 friends:")
        for loc in locations:
            arr = m[arrival[loc]].as_long()
            dep = m[departure[loc]].as_long()
            if arr != dep:
                print(f"{loc}: Arrive at {arr//60}:{arr%60:02d}, Depart at {dep//60}:{dep%60:02d}")
        for friend in friends:
            print(f"Met {friend}: {m[met[friend]]}")
        return
    
    s.pop()
    
    # If excluding Joseph didn't work, try excluding someone else
    # Try excluding Rebecca next
    s.push()
    s.add(Not(met['Rebecca']))
    s.add(And([met[f] for f in friends if f != 'Rebecca']))
    
    # Travel constraints for sequence: Financial -> Golden Gate -> Chinatown -> North Beach -> Union Square
    s.add(arrival['Golden_Gate_Park'] >= departure['Financial_District'] + travel_times[('Financial_District', 'Golden_Gate_Park')])
    s.add(arrival['Chinatown'] >= departure['Golden_Gate_Park'] + travel_times[('Golden_Gate_Park', 'Chinatown')])
    s.add(arrival['North_Beach'] >= departure['Chinatown'] + travel_times[('Chinatown', 'North_Beach')])
    s.add(arrival['Union_Square'] >= departure['North_Beach'] + travel_times[('North_Beach', 'Union_Square')])

    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found (excluding Rebecca)!")
        print("Meeting exactly 5 friends:")
        for loc in locations:
            arr = m[arrival[loc]].as_long()
            dep = m[departure[loc]].as_long()
            if arr != dep:
                print(f"{loc}: Arrive at {arr//60}:{arr%60:02d}, Depart at {dep//60}:{dep%60:02d}")
        for friend in friends:
            print(f"Met {friend}: {m[met[friend]]}")
        return
    
    s.pop()
    
    print("No feasible schedule found that meets exactly 5 friends.")

solve_scheduling()