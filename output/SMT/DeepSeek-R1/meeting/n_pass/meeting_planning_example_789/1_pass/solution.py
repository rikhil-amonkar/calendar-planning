from z3 import *

def main():
    # Define travel times dictionary
    travel_dict = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Sunset District'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Sunset District'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16
    }

    # Define friends data: name, location, start_avail (minutes from 9:00 AM), end_avail, min_duration
    friends = [
        {'name': 'Betty', 'location': 'Russian Hill', 'start_avail': -120, 'end_avail': 465, 'min_duration': 105},
        {'name': 'Melissa', 'location': 'Alamo Square', 'start_avail': 30, 'end_avail': 495, 'min_duration': 105},
        {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start_avail': 195, 'end_avail': 600, 'min_duration': 90},
        {'name': 'Jeffrey', 'location': 'Marina District', 'start_avail': 195, 'end_avail': 540, 'min_duration': 45},
        {'name': 'James', 'location': 'Bayview', 'start_avail': -90, 'end_avail': 660, 'min_duration': 90},
        {'name': 'Anthony', 'location': 'Chinatown', 'start_avail': 165, 'end_avail': 270, 'min_duration': 75},
        {'name': 'Timothy', 'location': 'Presidio', 'start_avail': 210, 'end_avail': 345, 'min_duration': 90},
        {'name': 'Emily', 'location': 'Sunset District', 'start_avail': 630, 'end_avail': 750, 'min_duration': 120}
    ]
    
    # Locations for all meetings: friends 0 to 7, and start meeting (index8) at Union Square
    locations = [f['location'] for f in friends] + ['Union Square']
    
    # Create Z3 solver with optimization
    opt = Optimize()
    
    # Number of friends (8) and total meetings (9, including start)
    n_friends = 8
    n_meetings = 9  # 8 friends + start
    
    # Variables for meetings: for friends (0 to 7) and start (index8)
    meet = [Bool(f"meet_{i}") for i in range(n_friends)]  # for friends 0..7
    s = [Int(f"s_{i}") for i in range(n_meetings)]        # start times for all 9 meetings
    e = [Int(f"e_{i}") for i in range(n_meetings)]        # end times for all 9 meetings
    
    # The start meeting (index8) is fixed
    opt.add(s[8] == 0)
    opt.add(e[8] == 0)
    
    # Before variables for every pair (i, j) with i < j
    before = {}
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            before[(i, j)] = Bool(f"before_{i}_{j}")
    
    # Constraints for each friend meeting
    for i in range(n_friends):
        # If we meet friend i, then the meeting must last at least min_duration
        opt.add(Implies(meet[i], e[i] == s[i] + friends[i]['min_duration']))
        # The meeting must occur within the friend's availability window
        opt.add(Implies(meet[i], s[i] >= friends[i]['start_avail']))
        opt.add(Implies(meet[i], e[i] <= friends[i]['end_avail']))
        # The start time must be non-negative (since we start at 9:00 AM)
        opt.add(Implies(meet[i], s[i] >= 0))
    
    # Constraints for the start meeting: already fixed, but we also note that the start meeting is always held.
    # For pairs involving the start meeting and a friend meeting
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            # Get travel times
            loc_i = locations[i]
            loc_j = locations[j]
            travel_ij = travel_dict.get((loc_i, loc_j))
            travel_ji = travel_dict.get((loc_j, loc_i))
            if travel_ij is None or travel_ji is None:
                # Should not happen, but skip if not found
                continue
                
            # Condition: both meetings are held. For the start meeting (index8), it is always held.
            condition_i = meet[i] if i < n_friends else True
            condition_j = meet[j] if j < n_friends else True
            condition = And(condition_i, condition_j)
            
            # If both are held, then enforce the order constraint
            # Case 1: i before j
            opt.add(Implies(And(condition, before[(i,j)]), e[i] + travel_ij <= s[j]))
            # Case 2: j before i
            opt.add(Implies(And(condition, Not(before[(i,j)])), e[j] + travel_ji <= s[i]))
    
    # Objective: maximize the number of friends met
    opt.maximize(Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    # Check and get the model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n_friends):
            if model.evaluate(meet[i]):
                start_minutes = model.evaluate(s[i])
                # Convert to integer
                if isinstance(start_minutes, IntNumRef):
                    start_val = start_minutes.as_long()
                else:
                    # If it's an expression, we try to get the value from the model
                    start_val = model.evaluate(s[i]).as_long()
                end_val = start_val + friends[i]['min_duration']
                # Convert minutes to time string (from 9:00 AM base)
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]['name'],
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: x['start_time'])
        print('SOLUTION:')
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()