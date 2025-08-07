from z3 import *

def main():
    # Define friends: each tuple contains (name, location, window_start (min from midnight), window_end, min_duration)
    friends = [
        ('Stephanie', 'Richmond', 16*60+15, 21*60+30, 75),
        ('William', 'Union Square', 10*60+45, 17*60+30, 45),
        ('Elizabeth', 'Nob Hill', 12*60+15, 15*60, 105),
        ('Joseph', 'Fisherman\'s Wharf', 12*60+45, 14*60, 75),
        ('Anthony', 'Golden Gate Park', 13*60, 20*60+30, 75),
        ('Barbara', 'Embarcadero', 19*60+15, 20*60+30, 75),
        ('Carol', 'Financial District', 11*60+45, 16*60+15, 60),
        ('Sandra', 'North Beach', 10*60, 12*60+30, 15),
        ('Kenneth', 'Presidio', 21*60+15, 22*60+15, 45)
    ]
    
    # Travel times dictionary: travel_dict[from_location][to_location] = minutes
    travel_dict = {
        "Marina District": {
            "Richmond": 11, "Union Square": 16, "Nob Hill": 12, "Fisherman's Wharf": 10,
            "Golden Gate Park": 18, "Embarcadero": 14, "Financial District": 17, "North Beach": 11, "Presidio": 10
        },
        "Richmond": {
            "Marina District": 9, "Union Square": 21, "Nob Hill": 17, "Fisherman's Wharf": 18,
            "Golden Gate Park": 9, "Embarcadero": 19, "Financial District": 22, "North Beach": 17, "Presidio": 7
        },
        "Union Square": {
            "Marina District": 18, "Richmond": 20, "Nob Hill": 9, "Fisherman's Wharf": 15,
            "Golden Gate Park": 22, "Embarcadero": 11, "Financial District": 9, "North Beach": 10, "Presidio": 24
        },
        "Nob Hill": {
            "Marina District": 11, "Richmond": 14, "Union Square": 7, "Fisherman's Wharf": 10,
            "Golden Gate Park": 17, "Embarcadero": 9, "Financial District": 9, "North Beach": 8, "Presidio": 17
        },
        "Fisherman's Wharf": {
            "Marina District": 9, "Richmond": 18, "Union Square": 13, "Nob Hill": 11,
            "Golden Gate Park": 25, "Embarcadero": 8, "Financial District": 11, "North Beach": 6, "Presidio": 17
        },
        "Golden Gate Park": {
            "Marina District": 16, "Richmond": 7, "Union Square": 22, "Nob Hill": 20,
            "Fisherman's Wharf": 24, "Embarcadero": 25, "Financial District": 26, "North Beach": 23, "Presidio": 11
        },
        "Embarcadero": {
            "Marina District": 12, "Richmond": 21, "Union Square": 10, "Nob Hill": 10,
            "Fisherman's Wharf": 6, "Golden Gate Park": 25, "Financial District": 5, "North Beach": 5, "Presidio": 20
        },
        "Financial District": {
            "Marina District": 15, "Richmond": 21, "Union Square": 9, "Nob Hill": 8,
            "Fisherman's Wharf": 10, "Golden Gate Park": 23, "Embarcadero": 4, "North Beach": 7, "Presidio": 22
        },
        "North Beach": {
            "Marina District": 9, "Richmond": 18, "Union Square": 7, "Nob Hill": 7,
            "Fisherman's Wharf": 5, "Golden Gate Park": 22, "Embarcadero": 6, "Financial District": 8, "Presidio": 17
        },
        "Presidio": {
            "Marina District": 11, "Richmond": 7, "Union Square": 22, "Nob Hill": 18,
            "Fisherman's Wharf": 19, "Golden Gate Park": 12, "Embarcadero": 20, "Financial District": 23, "North Beach": 18
        }
    }
    
    # Initialize Z3 solver
    opt = Optimize()
    
    # Create variables for each friend
    b_vars = {}  # Boolean: whether we meet the friend
    s_vars = {}  # Integer: start time (minutes from midnight)
    e_vars = {}  # Integer: end time (minutes from midnight)
    d_vars = {}  # Integer: duration of meeting
    
    for name, loc, start_win, end_win, min_dur in friends:
        b_vars[name] = Bool(f'b_{name}')
        s_vars[name] = Int(f's_{name}')
        e_vars[name] = Int(f'e_{name}')
        d_vars[name] = Int(f'd_{name}')
    
    # Starting time: 9:00 AM in minutes from midnight
    start_time_marina = 9 * 60
    
    # Constraints for each friend
    for name, loc, start_win, end_win, min_dur in friends:
        # If we meet the friend, then set constraints
        opt.add(Implies(b_vars[name], 
                      And(s_vars[name] >= start_win,
                          e_vars[name] <= end_win,
                          e_vars[name] == s_vars[name] + d_vars[name],
                          d_vars[name] >= min_dur)))
        
        # For Joseph and Barbara, fix their meeting times if met
        if name == 'Joseph':
            opt.add(Implies(b_vars[name], 
                           And(s_vars[name] == 12*60+45,
                               e_vars[name] == 14*60)))
        if name == 'Barbara':
            opt.add(Implies(b_vars[name],
                           And(s_vars[name] == 19*60+15,
                               e_vars[name] == 20*60+30)))
    
    # Constraint: start time must be at least start_time_marina + travel time from Marina to the friend's location
    for name, loc, start_win, end_win, min_dur in friends:
        travel_time = travel_dict["Marina District"][loc]
        opt.add(Implies(b_vars[name], s_vars[name] >= start_time_marina + travel_time))
    
    # Constraints for every pair of distinct friends
    n = len(friends)
    for i in range(n):
        name_i, loc_i, start_win_i, end_win_i, min_dur_i = friends[i]
        for j in range(i+1, n):
            name_j, loc_j, start_win_j, end_win_j, min_dur_j = friends[j]
            # Travel times between the two locations
            t_ij = travel_dict[loc_i][loc_j]
            t_ji = travel_dict[loc_j][loc_i]
            # If both friends are met, then either i before j or j before i with travel time
            opt.add(Implies(And(b_vars[name_i], b_vars[name_j]),
                           Or(e_vars[name_i] + t_ij <= s_vars[name_j],
                              e_vars[name_j] + t_ji <= s_vars[name_i])))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(b_vars[name], 1, 0) for name in b_vars])
    opt.maximize(objective)
    
    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        # Collect the meetings
        meetings = []
        for name, loc, start_win, end_win, min_dur in friends:
            if model.evaluate(b_vars[name]):
                start_val = model.evaluate(s_vars[name]).as_long()
                end_val = model.evaluate(e_vars[name]).as_long()
                # Format start and end times
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                meetings.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start time
        meetings.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
        # Output as JSON
        print({
            "itinerary": meetings
        })
    else:
        print('No solution found')

if __name__ == '__main__':
    main()