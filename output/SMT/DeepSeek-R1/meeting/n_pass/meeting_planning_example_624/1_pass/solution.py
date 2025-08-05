from z3 import *

def main():
    # Define travel time matrix
    travel = {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "The Castro": 13,
            "Chinatown": 23,
            "Alamo Square": 10,
            "North Beach": 24,
            "Russian Hill": 19
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Fisherman's Wharf": 23,
            "The Castro": 6,
            "Chinatown": 19,
            "Alamo Square": 5,
            "North Beach": 19,
            "Russian Hill": 17
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Haight-Ashbury": 22,
            "The Castro": 26,
            "Chinatown": 12,
            "Alamo Square": 20,
            "North Beach": 6,
            "Russian Hill": 7
        },
        "The Castro": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 6,
            "Fisherman's Wharf": 24,
            "Chinatown": 20,
            "Alamo Square": 8,
            "North Beach": 20,
            "Russian Hill": 18
        },
        "Chinatown": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Fisherman's Wharf": 8,
            "The Castro": 22,
            "Alamo Square": 17,
            "North Beach": 3,
            "Russian Hill": 7
        },
        "Alamo Square": {
            "Golden Gate Park": 9,
            "Haight-Ashbury": 5,
            "Fisherman's Wharf": 19,
            "The Castro": 8,
            "Chinatown": 16,
            "North Beach": 15,
            "Russian Hill": 13
        },
        "North Beach": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Fisherman's Wharf": 5,
            "The Castro": 22,
            "Chinatown": 6,
            "Alamo Square": 16,
            "Russian Hill": 4
        },
        "Russian Hill": {
            "Golden Gate Park": 21,
            "Haight-Ashbury": 17,
            "Fisherman's Wharf": 7,
            "The Castro": 21,
            "Chinatown": 9,
            "Alamo Square": 15,
            "North Beach": 5
        }
    }
    
    # Define friends' data (times in minutes from 9:00 AM)
    friends = [
        {'name': 'Carol', 'location': 'Haight-Ashbury', 'start_avail': 750, 'end_avail': 810, 'min_dur': 60},
        {'name': 'Laura', 'location': "Fisherman's Wharf", 'start_avail': 165, 'end_avail': 750, 'min_dur': 60},
        {'name': 'Karen', 'location': "The Castro", 'start_avail': 0, 'end_avail': 300, 'min_dur': 75},
        {'name': 'Elizabeth', 'location': "Chinatown", 'start_avail': 195, 'end_avail': 750, 'min_dur': 75},
        {'name': 'Deborah', 'location': "Alamo Square", 'start_avail': 180, 'end_avail': 360, 'min_dur': 105},
        {'name': 'Jason', 'location': "North Beach", 'start_avail': 345, 'end_avail': 600, 'min_dur': 90},
        {'name': 'Steven', 'location': "Russian Hill", 'start_avail': 345, 'end_avail': 570, 'min_dur': 120}
    ]
    
    # Create Z3 variables
    meet_vars = [Bool(f"meet_{f['name']}") for f in friends]
    start_vars = [Int(f"start_{f['name']}") for f in friends]
    end_vars = [Int(f"end_{f['name']}") for f in friends]
    
    # Initialize solver with optimization
    opt = Optimize()
    
    # Add constraints for each friend
    for i, friend in enumerate(friends):
        meet = meet_vars[i]
        start = start_vars[i]
        end = end_vars[i]
        
        # If meeting, constrain within window and duration
        opt.add(If(meet,
                   And(start >= friend['start_avail'],
                       start <= friend['end_avail'] - friend['min_dur'],
                       end == start + friend['min_dur']),
                   True))
    
    # Travel constraints from start location (Golden Gate Park)
    start_loc = "Golden Gate Park"
    for i, friend in enumerate(friends):
        loc = friend['location']
        travel_time = travel[start_loc][loc]
        opt.add(If(meet_vars[i], start_vars[i] >= travel_time, True))
    
    # Travel constraints between every pair of friends
    n = len(friends)
    for i in range(n):
        for j in range(i+1, n):
            meet_i = meet_vars[i]
            meet_j = meet_vars[j]
            start_i = start_vars[i]
            end_i = end_vars[i]
            loc_i = friends[i]['location']
            start_j = start_vars[j]
            end_j = end_vars[j]
            loc_j = friends[j]['location']
            
            travel_ij = travel[loc_i][loc_j]
            travel_ji = travel[loc_j][loc_i]
            
            opt.add(If(And(meet_i, meet_j),
                       Or(start_j >= end_i + travel_ij,
                          start_i >= end_j + travel_ji),
                       True))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Check and get the model
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for i, friend in enumerate(friends):
            if m.evaluate(meet_vars[i]):
                start_val = m.evaluate(start_vars[i]).as_long()
                end_val = m.evaluate(end_vars[i]).as_long()
                
                # Convert to absolute time (from minutes to HH:MM)
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                
                scheduled_meetings.append({
                    'person': friend['name'],
                    'start': start_val,
                    'start_str': start_str,
                    'end_str': end_str
                })
        
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x['start'])
        itinerary = [{
            "action": "meet",
            "person": mtg['person'],
            "start_time": mtg['start_str'],
            "end_time": mtg['end_str']
        } for mtg in scheduled_meetings]
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()