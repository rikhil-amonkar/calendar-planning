from z3 import *
import json

def main():
    # Friend data
    friends = {
        'Emily': {
            'location': 'Richmond District',
            'min_duration': 15,
            'available_start': 19 * 60,      # 7:00 PM
            'available_end': 21 * 60         # 9:00 PM
        },
        'Margaret': {
            'location': 'Financial District',
            'min_duration': 75,
            'available_start': 16 * 60 + 30, # 4:30 PM
            'available_end': 20 * 60 + 15    # 8:15 PM
        },
        'Ronald': {
            'location': 'North Beach',
            'min_duration': 45,
            'available_start': 18 * 60 + 30, # 6:30 PM
            'available_end': 19 * 60 + 30    # 7:30 PM
        },
        'Deborah': {
            'location': 'The Castro',
            'min_duration': 90,
            'available_start': 13 * 60 + 45, # 1:45 PM
            'available_end': 21 * 60 + 15    # 9:15 PM
        },
        'Jeffrey': {
            'location': 'Golden Gate Park',
            'min_duration': 120,
            'available_start': 11 * 60 + 15, # 11:15 AM
            'available_end': 14 * 60 + 30    # 2:30 PM
        }
    }
    
    # Travel times dictionary
    travel_times = {
        'Nob Hill': {
            'Richmond District': 14,
            'Financial District': 9,
            'North Beach': 8,
            'The Castro': 17,
            'Golden Gate Park': 17
        },
        'Richmond District': {
            'Nob Hill': 17,
            'Financial District': 22,
            'North Beach': 17,
            'The Castro': 16,
            'Golden Gate Park': 9
        },
        'Financial District': {
            'Nob Hill': 8,
            'Richmond District': 21,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'North Beach': {
            'Nob Hill': 7,
            'Richmond District': 18,
            'Financial District': 8,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Nob Hill': 16,
            'Richmond District': 16,
            'Financial District': 20,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Richmond District': 7,
            'Financial District': 26,
            'North Beach': 24,
            'The Castro': 13
        }
    }
    
    # Initialize solver
    opt = Optimize()
    
    # Create variables
    meet_vars = {name: Bool(f"meet_{name}") for name in friends}
    start_vars = {name: Int(f"start_{name}") for name in friends}
    end_vars = {name: Int(f"end_{name}") for name in friends}
    max_end = Int('max_end')
    
    # Base constraints for each friend
    for name, data in friends.items():
        # If meeting, enforce availability and duration
        opt.add(Implies(meet_vars[name], 
                      And(start_vars[name] >= data['available_start'],
                          end_vars[name] <= data['available_end'],
                          end_vars[name] == start_vars[name] + data['min_duration'])))
        # Start time must account for travel from Nob Hill
        opt.add(Implies(meet_vars[name],
                      start_vars[name] >= 9*60 + travel_times['Nob Hill'][data['location']]))
        # max_end must be at least the end time of each meeting
        opt.add(If(meet_vars[name], max_end >= end_vars[name], max_end >= 0))
    
    # Pairwise constraints for every distinct pair of friends
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            name_i, name_j = names[i], names[j]
            loc_i = friends[name_i]['location']
            loc_j = friends[name_j]['location']
            travel_i_to_j = travel_times[loc_i][loc_j]
            travel_j_to_i = travel_times[loc_j][loc_i]
            # If both meetings happen, ensure travel time between them
            opt.add(Implies(And(meet_vars[name_i], meet_vars[name_j]),
                          Or(start_vars[name_i] >= end_vars[name_j] + travel_j_to_i,
                             start_vars[name_j] >= end_vars[name_i] + travel_i_to_j)))
    
    # Objectives: first maximize number of meetings, then minimize max_end
    num_meetings = Sum([If(meet_vars[name], 1, 0) for name in friends])
    opt.maximize(num_meetings)
    opt.minimize(max_end)
    
    # Solve and output
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if m.evaluate(meet_vars[name]):
                start_val = m.evaluate(start_vars[name]).as_long()
                end_val = m.evaluate(end_vars[name]).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()