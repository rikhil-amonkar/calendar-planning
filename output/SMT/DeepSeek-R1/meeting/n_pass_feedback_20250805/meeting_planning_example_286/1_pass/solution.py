import itertools
import json
from z3 import *

def main():
    friends = [
        {'name': 'Carol', 'location': 'Sunset District', 'start_avail': 75, 'end_avail': 165, 'duration': 30},
        {'name': 'Karen', 'location': 'Bayview', 'start_avail': 225, 'end_avail': 360, 'duration': 120},
        {'name': 'Rebecca', 'location': 'Mission District', 'start_avail': 150, 'end_avail': 675, 'duration': 120}
    ]
    
    travel_times = {
        'Union Square': {'Sunset District': 26, 'Bayview': 15, 'Mission District': 14},
        'Sunset District': {'Union Square': 30, 'Bayview': 22, 'Mission District': 24},
        'Bayview': {'Union Square': 17, 'Sunset District': 23, 'Mission District': 13},
        'Mission District': {'Union Square': 15, 'Sunset District': 24, 'Bayview': 15}
    }
    
    perms = list(itertools.permutations([0, 1, 2]))
    solver = Solver()
    best_solution = None
    max_meetings = 0
    
    for perm in perms:
        s = [Int(f's_{i}') for i in range(3)]
        constraints = []
        
        f0 = friends[perm[0]]
        start_loc = 'Union Square'
        travel0 = travel_times[start_loc][f0['location']]
        constraints.append(s[0] >= travel0)
        constraints.append(s[0] >= f0['start_avail'])
        constraints.append(s[0] + f0['duration'] <= f0['end_avail'])
        
        f1 = friends[perm[1]]
        travel1 = travel_times[f0['location']][f1['location']]
        constraints.append(s[1] >= s[0] + f0['duration'] + travel1)
        constraints.append(s[1] >= f1['start_avail'])
        constraints.append(s[1] + f1['duration'] <= f1['end_avail'])
        
        f2 = friends[perm[2]]
        travel2 = travel_times[f1['location']][f2['location']]
        constraints.append(s[2] >= s[1] + f1['duration'] + travel2)
        constraints.append(s[2] >= f2['start_avail'])
        constraints.append(s[2] + f2['duration'] <= f2['end_avail'])
        
        solver.push()
        solver.add(constraints)
        if solver.check() == sat:
            m = solver.model()
            s0_val = m[s[0]].as_long()
            s1_val = m[s[1]].as_long()
            s2_val = m[s[2]].as_long()
            
            def min_to_time(mins):
                total_mins = 9 * 60 + mins
                h = total_mins // 60
                m = total_mins % 60
                return f"{h:02d}:{m:02d}"
            
            itinerary = [
                {'action': 'meet', 'person': f0['name'], 'start_time': min_to_time(s0_val), 'end_time': min_to_time(s0_val + f0['duration'])},
                {'action': 'meet', 'person': f1['name'], 'start_time': min_to_time(s1_val), 'end_time': min_to_time(s1_val + f1['duration'])},
                {'action': 'meet', 'person': f2['name'], 'start_time': min_to_time(s2_val), 'end_time': min_to_time(s2_val + f2['duration'])}
            ]
            best_solution = itinerary
            max_meetings = 3
            solver.pop()
            break
        solver.pop()
    
    if max_meetings == 0:
        pairs = list(itertools.combinations([0, 1, 2], 2))
        for pair in pairs:
            orders = list(itertools.permutations(pair))
            for order in orders:
                s = [Int(f's_{i}') for i in range(2)]
                constraints = []
                
                f0 = friends[order[0]]
                start_loc = 'Union Square'
                travel0 = travel_times[start_loc][f0['location']]
                constraints.append(s[0] >= travel0)
                constraints.append(s[0] >= f0['start_avail'])
                constraints.append(s[0] + f0['duration'] <= f0['end_avail'])
                
                f1 = friends[order[1]]
                travel1 = travel_times[f0['location']][f1['location']]
                constraints.append(s[1] >= s[0] + f0['duration'] + travel1)
                constraints.append(s[1] >= f1['start_avail'])
                constraints.append(s[1] + f1['duration'] <= f1['end_avail'])
                
                solver.push()
                solver.add(constraints)
                if solver.check() == sat:
                    m = solver.model()
                    s0_val = m[s[0]].as_long()
                    s1_val = m[s[1]].as_long()
                    
                    def min_to_time(mins):
                        total_mins = 9 * 60 + mins
                        h = total_mins // 60
                        m = total_mins % 60
                        return f"{h:02d}:{m:02d}"
                    
                    itinerary = [
                        {'action': 'meet', 'person': f0['name'], 'start_time': min_to_time(s0_val), 'end_time': min_to_time(s0_val + f0['duration'])},
                        {'action': 'meet', 'person': f1['name'], 'start_time': min_to_time(s1_val), 'end_time': min_to_time(s1_val + f1['duration'])}
                    ]
                    best_solution = itinerary
                    max_meetings = 2
                    solver.pop()
                    break
                solver.pop()
            if max_meetings == 2:
                break
    
    if best_solution is None:
        for i in range(3):
            s0 = Int('s0')
            solver.push()
            f = friends[i]
            travel0 = travel_times['Union Square'][f['location']]
            solver.add(s0 >= travel0)
            solver.add(s0 >= f['start_avail'])
            solver.add(s0 + f['duration'] <= f['end_avail'])
            if solver.check() == sat:
                m = solver.model()
                s0_val = m[s0].as_long()
                def min_to_time(mins):
                    total_mins = 9 * 60 + mins
                    h = total_mins // 60
                    m = total_mins % 60
                    return f"{h:02d}:{m:02d}"
                best_solution = [{'action': 'meet', 'person': f['name'], 'start_time': min_to_time(s0_val), 'end_time': min_to_time(s0_val + f['duration'])}]
                max_meetings = 1
                solver.pop()
                break
            solver.pop()
    
    if best_solution is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": best_solution}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()