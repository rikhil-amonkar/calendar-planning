from z3 import *
import itertools
import json

def main():
    # Define travel times dictionary
    travel = {
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Financial District'): 13,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Financial District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Haight-Ashbury'): 19
    }
    
    # Friend data: name, location, duration, availability_start (min), availability_end (min)
    friends = [
        ('Mary', 'Pacific Heights', 45, 60, 600),
        ('Lisa', 'Mission District', 75, 690, 780),
        ('Betty', 'Haight-Ashbury', 90, 0, 495),
        ('Charles', 'Financial District', 120, 135, 360)
    ]
    
    s = Optimize()
    
    # Create variables
    m_vars = {}
    s_vars = {}
    for name, loc, dur, start_avail, end_avail in friends:
        m_vars[name] = Bool(f'm_{name}')
        s_vars[name] = Int(f's_{name}')
    
    # Individual constraints
    for name, loc, dur, start_avail, end_avail in friends:
        m = m_vars[name]
        s_val = s_vars[name]
        # If meeting this friend, then constraints
        s.add(Implies(m, s_val >= start_avail))
        s.add(Implies(m, s_val + dur <= end_avail))
        # Travel time from Bayview to this location
        s.add(Implies(m, s_val >= travel[('Bayview', loc)]))
    
    # Pairwise disjunctive constraints
    pairs = list(itertools.combinations(friends, 2))
    for (f1, f2) in pairs:
        name1, loc1, dur1, sa1, ea1 = f1
        name2, loc2, dur2, sa2, ea2 = f2
        m1 = m_vars[name1]
        m2 = m_vars[name2]
        s1 = s_vars[name1]
        s2 = s_vars[name2]
        # Travel time from loc1 to loc2 and loc2 to loc1
        travel_1_to_2 = travel[(loc1, loc2)]
        travel_2_to_1 = travel[(loc2, loc1)]
        # Constraint: if both meetings happen, they must not overlap and account for travel
        s.add(Implies(And(m1, m2),
                      Or( s1 + dur1 + travel_1_to_2 <= s2,
                          s2 + dur2 + travel_2_to_1 <= s1 )))
    
    # Objective: maximize the number of meetings
    total_meetings = Sum([If(m_vars[name], 1, 0) for name in m_vars])
    s.maximize(total_meetings)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        meetings_list = []
        for name, loc, dur, sa, ea in friends:
            if model.evaluate(m_vars[name]):
                start_val = model.evaluate(s_vars[name])
                start_minutes = start_val.as_long()
                end_minutes = start_minutes + dur
                start_hour = 9 + start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = 9 + end_minutes // 60
                end_minute = end_minutes % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                meetings_list.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort meetings by start_time
        meetings_list.sort(key=lambda x: x['start_time'])
        result = {"itinerary": meetings_list}
    else:
        result = {"itinerary": []}
    
    # Output the solution
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == '__main__':
    main()