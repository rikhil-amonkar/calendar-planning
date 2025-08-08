import json
from z3 import *

def main():
    travel_text = """
    The Castro to Marina District: 21.
    The Castro to Presidio: 20.
    The Castro to North Beach: 20.
    The Castro to Embarcadero: 22.
    The Castro to Haight-Ashbury: 6.
    The Castro to Golden Gate Park: 11.
    The Castro to Richmond District: 16.
    The Castro to Alamo Square: 8.
    The Castro to Financial District: 21.
    The Castro to Sunset District: 17.
    Marina District to The Castro: 22.
    Marina District to Presidio: 10.
    Marina District to North Beach: 11.
    Marina District to Embarcadero: 14.
    Marina District to Haight-Ashbury: 16.
    Marina District to Golden Gate Park: 18.
    Marina District to Richmond District: 11.
    Marina District to Alamo Square: 15.
    Marina District to Financial District: 17.
    Marina District to Sunset District: 19.
    Presidio to The Castro: 21.
    Presidio to Marina District: 10.
    Presidio to North Beach: 18.
    Presidio to Embarcadero: 20.
    Presidio to Haight-Ashbury: 15.
    Presidio to Golden Gate Park: 12.
    Presidio to Richmond District: 7.
    Presidio to Alamo Square: 19.
    Presidio to Financial District: 23.
    Presidio to Sunset District: 15.
    North Beach to The Castro: 23.
    North Beach to Marina District: 9.
    North Beach to Presidio: 17.
    North Beach to Embarcadero: 6.
    North Beach to Haight-Ashbury: 18.
    North Beach to Golden Gate Park: 22.
    North Beach to Richmond District: 18.
    North Beach to Alamo Square: 16.
    North Beach to Financial District: 8.
    North Beach to Sunset District: 27.
    Embarcadero to The Castro: 25.
    Embarcadero to Marina District: 12.
    Embarcadero to Presidio: 20.
    Embarcadero to North Beach: 5.
    Embarcadero to Haight-Ashbury: 21.
    Embarcadero to Golden Gate Park: 25.
    Embarcadero to Richmond District: 21.
    Embarcadero to Alamo Square: 19.
    Embarcadero to Financial District: 5.
    Embarcadero to Sunset District: 30.
    Haight-Ashbury to The Castro: 6.
    Haight-Ashbury to Marina District: 17.
    Haight-Ashbury to Presidio: 15.
    Haight-Ashbury to North Beach: 19.
    Haight-Ashbury to Embarcadero: 20.
    Haight-Ashbury to Golden Gate Park: 7.
    Haight-Ashbury to Richmond District: 10.
    Haight-Ashbury to Alamo Square: 5.
    Haight-Ashbury to Financial District: 21.
    Haight-Ashbury to Sunset District: 15.
    Golden Gate Park to The Castro: 13.
    Golden Gate Park to Marina District: 16.
    Golden Gate Park to Presidio: 11.
    Golden Gate Park to North Beach: 23.
    Golden Gate Park to Embarcadero: 25.
    Golden Gate Park to Haight-Ashbury: 7.
    Golden Gate Park to Richmond District: 7.
    Golden Gate Park to Alamo Square: 9.
    Golden Gate Park to Financial District: 26.
    Golden Gate Park to Sunset District: 10.
    Richmond District to The Castro: 16.
    Richmond District to Marina District: 9.
    Richmond District to Presidio: 7.
    Richmond District to North Beach: 17.
    Richmond District to Embarcadero: 19.
    Richmond District to Haight-Ashbury: 10.
    Richmond District to Golden Gate Park: 9.
    Richmond District to Alamo Square: 13.
    Richmond District to Financial District: 22.
    Richmond District to Sunset District: 11.
    Alamo Square to The Castro: 8.
    Alamo Square to Marina District: 15.
    Alamo Square to Presidio: 17.
    Alamo Square to North Beach: 15.
    Alamo Square to Embarcadero: 16.
    Alamo Square to Haight-Ashbury: 5.
    Alamo Square to Golden Gate Park: 9.
    Alamo Square to Richmond District: 11.
    Alamo Square to Financial District: 17.
    Alamo Square to Sunset District: 16.
    Financial District to The Castro: 20.
    Financial District to Marina District: 15.
    Financial District to Presidio: 22.
    Financial District to North Beach: 7.
    Financial District to Embarcadero: 4.
    Financial District to Haight-Ashbury: 19.
    Financial District to Golden Gate Park: 23.
    Financial District to Richmond District: 21.
    Financial District to Alamo Square: 17.
    Financial District to Sunset District: 30.
    Sunset District to The Castro: 17.
    Sunset District to Marina District: 21.
    Sunset District to Presidio: 16.
    Sunset District to North Beach: 28.
    Sunset District to Embarcadero: 30.
    Sunset District to Haight-Ashbury: 15.
    Sunset District to Golden Gate Park: 11.
    Sunset District to Richmond District: 12.
    Sunset District to Alamo Square: 17.
    Sunset District to Financial District: 30.
    """

    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.endswith('.'):
            line = line[:-1]
        parts = line.split(':')
        if len(parts) < 2:
            continue
        left_part = parts[0].strip()
        right_part = parts[1].strip().rstrip('.')
        try:
            time_val = int(right_part)
        except:
            continue
        if ' to ' not in left_part:
            continue
        locs = left_part.split(' to ')
        if len(locs) != 2:
            continue
        from_loc = locs[0].strip()
        to_loc = locs[1].strip()
        if from_loc not in travel_dict:
            travel_dict[from_loc] = {}
        travel_dict[from_loc][to_loc] = time_val

    friends = [
        ("Elizabeth", "Marina District", 19*60, 20*60+45, 105),
        ("Joshua", "Presidio", 8*60+30, 13*60+15, 105),
        ("Timothy", "North Beach", 19*60+45, 22*60, 90),
        ("David", "Embarcadero", 10*60+45, 12*60+30, 30),
        ("Kimberly", "Haight-Ashbury", 16*60+45, 21*60+30, 75),
        ("Lisa", "Golden Gate Park", 17*60+30, 21*60+45, 45),
        ("Ronald", "Richmond District", 8*60, 9*60+30, 90),
        ("Stephanie", "Alamo Square", 15*60+30, 16*60+30, 30),
        ("Helen", "Financial District", 17*60+30, 18*60+30, 45),
        ("Laura", "Sunset District", 17*60+45, 21*60+15, 90),
    ]
    
    meetings = [("Start", "The Castro", 540, 540, 0)]
    for friend in friends:
        meetings.append(friend)
    
    n = len(meetings) - 1  # number of friends (excluding dummy)
    
    solution_found = False
    result_schedule = []
    
    for k in range(n, 0, -1):
        s = Solver()
        s.set("timeout", 30000)  # 30 seconds per k
        
        selected = [None] * len(meetings)
        start = [None] * len(meetings)
        end = [None] * len(meetings)
        
        selected[0] = True
        start[0] = 540
        end[0] = 540
        
        for i in range(1, len(meetings)):
            selected[i] = Bool(f"selected_{i}")
            start[i] = Int(f"start_{i}")
            end[i] = Int(f"end_{i}")
        
        for i in range(1, len(meetings)):
            name, loc, avail_start, avail_end, min_dur = meetings[i]
            s.add(Implies(selected[i], 
                          And(start[i] >= avail_start,
                              end[i] <= avail_end,
                              end[i] - start[i] >= min_dur)))
        
        s.add(Sum([If(selected[i], 1, 0) for i in range(1, len(meetings))]) == k)
        
        for i in range(len(meetings)):
            for j in range(i+1, len(meetings)):
                if i == 0 and j == 0:
                    continue
                loc_i = meetings[i][1]
                loc_j = meetings[j][1]
                travel_ij = travel_dict[loc_i][loc_j]
                travel_ji = travel_dict[loc_j][loc_i]
                s.add(Implies(And(selected[i], selected[j]),
                              Or(end[i] + travel_ij <= start[j],
                                 end[j] + travel_ji <= start[i])))
        
        if s.check() == sat:
            model = s.model()
            selected_friends = []
            for i in range(1, len(meetings)):
                if is_true(model.eval(selected[i])):
                    name = meetings[i][0]
                    start_val = model.eval(start[i]).as_long()
                    end_val = model.eval(end[i]).as_long()
                    start_h = start_val // 60
                    start_m = start_val % 60
                    end_h = end_val // 60
                    end_m = end_val % 60
                    start_str = f"{start_h:02d}:{start_m:02d}"
                    end_str = f"{end_h:02d}:{end_m:02d}"
                    selected_friends.append((start_val, name, start_str, end_str))
            selected_friends.sort(key=lambda x: x[0])
            itinerary = [{"action": "meet", "person": name, "start_time": start_str, "end_time": end_str} 
                         for (_, name, start_str, end_str) in selected_friends]
            result_schedule = itinerary
            solution_found = True
            break
    
    if solution_found:
        result = {"itinerary": result_schedule}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()