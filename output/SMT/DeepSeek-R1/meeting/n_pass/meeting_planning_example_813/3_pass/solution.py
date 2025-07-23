from z3 import *

def main():
    meetings = []
    meetings.append({
        'name': 'Start',
        'loc': 'Marina District',
        'start_min': 540,
        'end_min': 540,
        'min_time': 0,
        'available_start': 540,
        'available_end': 540
    })

    friends_info = [
        {"name": "Joshua", "loc": "Embarcadero", "start": "9:45", "end": "18:00", "min": 105},
        {"name": "Jeffrey", "loc": "Bayview", "start": "9:45", "end": "20:15", "min": 75},
        {"name": "Charles", "loc": "Union Square", "start": "10:45", "end": "20:15", "min": 120},
        {"name": "Joseph", "loc": "Chinatown", "start": "7:00", "end": "15:30", "min": 60},
        {"name": "Matthew", "loc": "Golden Gate Park", "start": "11:00", "end": "19:30", "min": 45},
        {"name": "Carol", "loc": "Financial District", "start": "10:45", "end": "11:15", "min": 15},
        {"name": "Paul", "loc": "Haight-Ashbury", "start": "19:15", "end": "20:30", "min": 15},
        {"name": "Rebecca", "loc": "Mission District", "start": "17:00", "end": "21:45", "min": 45}
    ]

    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    for friend in friends_info:
        start_min = time_str_to_minutes(friend['start'])
        end_min = time_str_to_minutes(friend['end'])
        meetings.append({
            'name': friend['name'],
            'loc': friend['loc'],
            'min_time': friend['min'],
            'available_start': start_min,
            'available_end': end_min
        })

    travel_times = {
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Mission District"): 20,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Mission District"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Mission District"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12
    }

    s = Solver()
    opt = Optimize()

    n = len(meetings)
    for idx in range(1, n):
        meetings[idx]['meet_var'] = Bool(f"meet_{idx}")
        meetings[idx]['s_var'] = Int(f"s_{idx}")
        meetings[idx]['e_var'] = Int(f"e_{idx}")

    # Sequence variables to enforce total order
    seq_vars = [Int(f"seq_{i}") for i in range(1, n)]
    for var in seq_vars:
        opt.add(var >= 1, var <= n-1)

    opt.add(Distinct(seq_vars))

    for idx in range(1, n):
        meet_var = meetings[idx]['meet_var']
        s_var = meetings[idx]['s_var']
        e_var = meetings[idx]['e_var']
        min_time = meetings[idx]['min_time']
        available_start = meetings[idx]['available_start']
        available_end = meetings[idx]['available_end']
        
        opt.add(Implies(meet_var, And(
            s_var >= available_start,
            e_var == s_var + min_time,
            e_var <= available_end,
            seq_vars[idx-1] == idx  # Only set sequence for selected meetings
        )))
        
        opt.add(Implies(Not(meet_var), seq_vars[idx-1] != idx)

    # Constraints for travel from initial meeting
    for j in range(1, n):
        meet_j = meetings[j]['meet_var']
        loc_j = meetings[j]['loc']
        travel_time = travel_times[(meetings[0]['loc'], loc_j)]
        opt.add(Implies(meet_j, meetings[j]['s_var'] >= meetings[0]['end_min'] + travel_time))

    # Constraints between consecutive meetings in sequence
    for i in range(1, n):
        for j in range(1, n):
            if i == j:
                continue
            meet_i = meetings[i]['meet_var']
            meet_j = meetings[j]['meet_var']
            loc_i = meetings[i]['loc']
            loc_j = meetings[j]['loc']
            travel_time = travel_times[(loc_i, loc_j)]
            
            # j immediately follows i in the sequence
            seq_condition = And(seq_vars[i-1] + 1 == seq_vars[j-1])
            
            opt.add(Implies(And(meet_i, meet_j, seq_condition),
                     meetings[j]['s_var'] >= meetings[i]['e_var'] + travel_time))

    meet_vars = [meetings[i]['meet_var'] for i in range(1, n)]
    total_meet = Sum([If(var, 1, 0) for var in meet_vars])
    opt.maximize(total_meet)

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for idx in range(1, n):
            meet_var = meetings[idx]['meet_var']
            if is_true(m.eval(meet_var)):
                s_val = m.eval(meetings[idx]['s_var'])
                e_val = m.eval(meetings[idx]['e_var'])
                if isinstance(s_val, IntNumRef) and isinstance(e_val, IntNumRef):
                    s_min = s_val.as_long()
                    e_min = e_val.as_long()
                    start_hour = s_min // 60
                    start_minute = s_min % 60
                    end_hour = e_min // 60
                    end_minute = e_min % 60
                    start_time = f"{start_hour:02d}:{start_minute:02d}"
                    end_time = f"{end_hour:02d}:{end_minute:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": meetings[idx]['name'],
                        "start_time": start_time,
                        "end_time": end_time
                    })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]) * 60 + int(x['start_time'][3:5])))
        print("SOLUTION:")
        print({"itinerary": itinerary})
    else:
        print("SOLUTION:")
        print({"itinerary": []})

if __name__ == '__main__':
    main()