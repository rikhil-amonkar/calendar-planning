from z3 import *
import json

def main():
    friends = ['Brian', 'Richard', 'Ashley', 'Elizabeth', 'Jessica', 'Deborah', 'Kimberly', 'Kenneth', 'Anthony']
    
    available_start = {
        'Brian': 240,
        'Richard': 120,
        'Ashley': 360,
        'Elizabeth': 165,
        'Jessica': 660,
        'Deborah': 510,
        'Kimberly': 510,
        'Kenneth': 285,
        'Anthony': 315
    }
    
    available_end = {
        'Brian': 600,
        'Richard': 225,
        'Ashley': 690,
        'Elizabeth': 570,
        'Jessica': 765,
        'Deborah': 780,
        'Kimberly': 735,
        'Kenneth': 630,
        'Anthony': 420
    }
    
    min_duration = {
        'Brian': 90,
        'Richard': 60,
        'Ashley': 90,
        'Elizabeth': 75,
        'Jessica': 105,
        'Deborah': 60,
        'Kimberly': 45,
        'Kenneth': 105,
        'Anthony': 30
    }
    
    locations_dict = {
        'Bayview': 'Bayview',
        'Brian': 'North Beach',
        'Richard': 'Fisherman\'s Wharf',
        'Ashley': 'Haight-Ashbury',
        'Elizabeth': 'Nob Hill',
        'Jessica': 'Golden Gate Park',
        'Deborah': 'Union Square',
        'Kimberly': 'Alamo Square',
        'Kenneth': 'Chinatown',
        'Anthony': 'Pacific Heights'
    }
    
    travel_times = {
        'Bayview': {
            'North Beach': 22,
            'Fisherman\'s Wharf': 25,
            'Haight-Ashbury': 19,
            'Nob Hill': 20,
            'Golden Gate Park': 22,
            'Union Square': 18,
            'Alamo Square': 16,
            'Presidio': 32,
            'Chinatown': 19,
            'Pacific Heights': 23
        },
        'North Beach': {
            'Bayview': 25,
            'Fisherman\'s Wharf': 5,
            'Haight-Ashbury': 18,
            'Nob Hill': 7,
            'Golden Gate Park': 22,
            'Union Square': 7,
            'Alamo Square': 16,
            'Presidio': 17,
            'Chinatown': 6,
            'Pacific Heights': 8
        },
        'Fisherman\'s Wharf': {
            'Bayview': 26,
            'North Beach': 6,
            'Haight-Ashbury': 22,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Union Square': 13,
            'Alamo Square': 21,
            'Presidio': 17,
            'Chinatown': 12,
            'Pacific Heights': 12
        },
        'Haight-Ashbury': {
            'Bayview': 18,
            'North Beach': 19,
            'Fisherman\'s Wharf': 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Union Square': 19,
            'Alamo Square': 5,
            'Presidio': 15,
            'Chinatown': 19,
            'Pacific Heights': 12
        },
        'Nob Hill': {
            'Bayview': 19,
            'North Beach': 8,
            'Fisherman\'s Wharf': 10,
            'Haight-Ashbury': 13,
            'Golden Gate Park': 17,
            'Union Square': 7,
            'Alamo Square': 11,
            'Presidio': 17,
            'Chinatown': 6,
            'Pacific Heights': 8
        },
        'Golden Gate Park': {
            'Bayview': 23,
            'North Beach': 23,
            'Fisherman\'s Wharf': 24,
            'Haight-Ashbury': 7,
            'Nob Hill': 20,
            'Union Square': 22,
            'Alamo Square': 9,
            'Presidio': 11,
            'Chinatown': 23,
            'Pacific Heights': 16
        },
        'Union Square': {
            'Bayview': 15,
            'North Beach': 10,
            'Fisherman\'s Wharf': 15,
            'Haight-Ashbury': 18,
            'Nob Hill': 9,
            'Golden Gate Park': 22,
            'Alamo Square': 15,
            'Presidio': 24,
            'Chinatown': 7,
            'Pacific Heights': 15
        },
        'Alamo Square': {
            'Bayview': 16,
            'North Beach': 15,
            'Fisherman\'s Wharf': 19,
            'Haight-Ashbury': 5,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Union Square': 14,
            'Presidio': 17,
            'Chinatown': 15,
            'Pacific Heights': 10
        },
        'Presidio': {
            'Bayview': 31,
            'North Beach': 18,
            'Fisherman\'s Wharf': 19,
            'Haight-Ashbury': 15,
            'Nob Hill': 18,
            'Golden Gate Park': 12,
            'Union Square': 22,
            'Alamo Square': 19,
            'Chinatown': 21,
            'Pacific Heights': 11
        },
        'Chinatown': {
            'Bayview': 20,
            'North Beach': 3,
            'Fisherman\'s Wharf': 8,
            'Haight-Ashbury': 19,
            'Nob Hill': 9,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'Alamo Square': 17,
            'Presidio': 19,
            'Pacific Heights': 10
        },
        'Pacific Heights': {
            'Bayview': 22,
            'North Beach': 9,
            'Fisherman\'s Wharf': 13,
            'Haight-Ashbury': 11,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Union Square': 12,
            'Alamo Square': 10,
            'Presidio': 11,
            'Chinatown': 11
        }
    }
    
    nodes = ['Bayview'] + friends
    
    s = Optimize()
    
    meet = {}
    start = {}
    end = {}
    for f in friends:
        meet[f] = Bool(f)
        start[f] = Int(f'start_{f}')
        end[f] = Int(f'end_{f}')
    
    before = {}
    for i in nodes:
        before[i] = {}
        for j in nodes:
            if i != j:
                before[i][j] = Bool(f'before_{i}_{j}')
    
    for f in friends:
        s.add(If(meet[f],
                 And(
                     start[f] >= available_start[f],
                     end[f] == start[f] + min_duration[f],
                     end[f] <= available_end[f]
                 ),
                 True))
    
    for f in friends:
        travel_time = travel_times['Bayview'][locations_dict[f]]
        s.add(If(meet[f], start[f] >= travel_time, True))
    
    for f in friends:
        s.add(If(meet[f],
                 And(before['Bayview'][f], Not(before[f]['Bayview'])),
                 True))
    
    for i in nodes:
        for j in nodes:
            if i == j:
                continue
            active_i = True if i == 'Bayview' else meet[i]
            active_j = True if j == 'Bayview' else meet[j]
            
            if i == 'Bayview':
                start_i = 0
                end_i = 0
            else:
                start_i = start[i]
                end_i = end[i]
            
            if j == 'Bayview':
                start_j = 0
                end_j = 0
            else:
                start_j = start[j]
                end_j = end[j]
            
            loc_i = locations_dict[i]
            loc_j = locations_dict[j]
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]
            
            s.add(Implies(And(active_i, active_j),
                         And(
                             Or(before[i][j], before[j][i]),
                             Not(And(before[i][j], before[j][i])),
                             Implies(before[i][j], end_i + travel_ij <= start_j),
                             Implies(before[j][i], end_j + travel_ji <= start_i)
                         )))
    
    total_meetings = Sum([If(meet[f], 1, 0) for f in friends])
    s.maximize(total_meetings)
    
    if s.check() == sat:
        model = s.model()
        meetings_list = []
        for f in friends:
            if is_true(model[meet[f]]):
                start_val = model.eval(start[f])
                end_val = model.eval(end[f])
                if isinstance(start_val, IntNumRef):
                    start_minutes = start_val.as_long()
                else:
                    start_minutes = int(str(start_val))
                if isinstance(end_val, IntNumRef):
                    end_minutes = end_val.as_long()
                else:
                    end_minutes = int(str(end_val))
                
                start_hour = 9 + start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = 9 + end_minutes // 60
                end_minute = end_minutes % 60
                
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                
                meetings_list.append( (start_minutes, f, start_str, end_str) )
        
        meetings_list.sort(key=lambda x: x[0])
        itinerary = []
        for (start_min, person, start_str, end_str) in meetings_list:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()