from z3 import *

def main():
    # Travel times dictionary
    travel_dict = {
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17
    }
    
    def get_travel_time(loc1, loc2):
        key = (loc1, loc2)
        if key in travel_dict:
            return travel_dict[key]
        key2 = (loc2, loc1)
        if key2 in travel_dict:
            return travel_dict[key2]
        return 0  # Default if not found (should not happen)

    meetings = [
        {"name": "virtual", "loc": "Richmond District", "start": 0, "end": 0, "met": True},
        {"name": "Sarah", "loc": "Sunset District", "min_start": 105, "max_end": 600, "duration": 30},
        {"name": "Richard", "loc": "Haight-Ashbury", "min_start": 165, "max_end": 405, "duration": 90},
        {"name": "Elizabeth", "loc": "Mission District", "min_start": 120, "max_end": 495, "duration": 120},
        {"name": "Michelle", "loc": "Golden Gate Park", "min_start": 555, "max_end": 705, "duration": 90}
    ]

    # Initialize Z3 variables for real meetings
    for i in range(1, len(meetings)):
        m = meetings[i]
        m['met_var'] = Bool(f"met_{m['name']}")
        m['start_var'] = Int(f"start_{m['name']}")
        m['end_var'] = Int(f"end_{m['name']}")

    opt = Optimize()

    # Add constraints for each meeting
    for i in range(1, len(meetings)):
        m = meetings[i]
        opt.add(Implies(m['met_var'], 
                       And(
                           m['start_var'] >= m['min_start'],
                           m['end_var'] == m['start_var'] + m['duration'],
                           m['end_var'] <= m['max_end']
                       )))

    # Add pairwise travel constraints
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            loc1 = m1['loc']
            loc2 = m2['loc']
            t12 = get_travel_time(loc1, loc2)
            t21 = get_travel_time(loc2, loc1)
            
            if i == 0:  # Virtual meeting
                # Only constraint: travel from virtual to real meeting
                opt.add(Implies(m2['met_var'], m1['end'] + t12 <= m2['start_var']))
            else:
                # Both are real meetings
                opt.add(Implies(And(m1['met_var'], m2['met_var']),
                               Or(
                                   m1['end_var'] + t12 <= m2['start_var'],
                                   m2['end_var'] + t21 <= m1['start_var']
                               )))

    # Maximize the number of meetings
    total_met = Sum([If(m['met_var'], 1, 0) for m in meetings[1:]])
    opt.maximize(total_met)

    if opt.check() == sat:
        model = opt.model()
        itinerary_list = []
        for i in range(1, len(meetings)):
            m = meetings[i]
            if model.evaluate(m['met_var']):
                start_val = model.evaluate(m['start_var'])
                # Convert Z3 Int to Python int
                start_minutes = start_val.as_long()
                end_minutes = start_minutes + m['duration']
                # Convert minutes to time string (since 9:00 AM)
                total_minutes_start = start_minutes
                hours_start = 9 + total_minutes_start // 60
                minutes_start = total_minutes_start % 60
                start_time_str = f"{hours_start:02d}:{minutes_start:02d}"
                
                total_minutes_end = end_minutes
                hours_end = 9 + total_minutes_end // 60
                minutes_end = total_minutes_end % 60
                end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
                
                itinerary_list.append({
                    "action": "meet",
                    "person": m['name'],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        
        # Sort by start time
        itinerary_list.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()