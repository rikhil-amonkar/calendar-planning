from z3 import *
import itertools
import json

def minutes_to_time_str(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    friends = [
        {'name': 'Emily', 'location': 'P', 'start_avail': 435, 'end_avail': 720, 'duration': 105},
        {'name': 'Joseph', 'location': 'R', 'start_avail': 495, 'end_avail': 780, 'duration': 120},
        {'name': 'Melissa', 'location': 'F', 'start_avail': 405, 'end_avail': 765, 'duration': 75}
    ]
    
    travel_times = {
        'FW': {'P': 17, 'R': 18, 'F': 11},
        'P': {'FW': 19, 'R': 7, 'F': 23},
        'R': {'FW': 18, 'P': 7, 'F': 22},
        'F': {'FW': 10, 'P': 22, 'R': 21}
    }
    
    itinerary = []
    found = False
    
    # Try to schedule three meetings
    perms = list(itertools.permutations([0, 1, 2]))
    for perm in perms:
        i, j, k = perm
        s0 = Int(f's0_{perm}')
        s1 = Int(f's1_{perm}')
        s2 = Int(f's2_{perm}')
        solver = Solver()
        
        # Constraints for the first meeting (friend i)
        travel0 = travel_times['FW'][friends[i]['location']]
        solver.add(s0 >= travel0)
        solver.add(s0 >= friends[i]['start_avail'])
        e0 = s0 + friends[i]['duration']
        solver.add(e0 <= friends[i]['end_avail'])
        
        # Constraints for the second meeting (friend j)
        travel1 = travel_times[friends[i]['location']][friends[j]['location']]
        solver.add(s1 >= e0 + travel1)
        solver.add(s1 >= friends[j]['start_avail'])
        e1 = s1 + friends[j]['duration']
        solver.add(e1 <= friends[j]['end_avail'])
        
        # Constraints for the third meeting (friend k)
        travel2 = travel_times[friends[j]['location']][friends[k]['location']]
        solver.add(s2 >= e1 + travel2)
        solver.add(s2 >= friends[k]['start_avail'])
        e2 = s2 + friends[k]['duration']
        solver.add(e2 <= friends[k]['end_avail'])
        
        if solver.check() == sat:
            m = solver.model()
            s0_val = m[s0].as_long()
            s1_val = m[s1].as_long()
            s2_val = m[s2].as_long()
            
            meeting0 = {
                "action": "meet",
                "person": friends[i]['name'],
                "start_time": minutes_to_time_str(s0_val),
                "end_time": minutes_to_time_str(s0_val + friends[i]['duration'])
            }
            meeting1 = {
                "action": "meet",
                "person": friends[j]['name'],
                "start_time": minutes_to_time_str(s1_val),
                "end_time": minutes_to_time_str(s1_val + friends[j]['duration'])
            }
            meeting2 = {
                "action": "meet",
                "person": friends[k]['name'],
                "start_time": minutes_to_time_str(s2_val),
                "end_time": minutes_to_time_str(s2_val + friends[k]['duration'])
            }
            itinerary = [meeting0, meeting1, meeting2]
            found = True
            break
    
    if found:
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # Try to schedule two meetings
    subsets = list(itertools.combinations([0,1,2], 2))
    for skip in range(3):
        indices = [idx for idx in [0,1,2] if idx != skip]
        orders = list(itertools.permutations(indices))
        for order in orders:
            i, j = order
            s0 = Int(f's0_{order}')
            s1 = Int(f's1_{order}')
            solver = Solver()
            
            # Constraints for the first meeting (friend i)
            travel0 = travel_times['FW'][friends[i]['location']]
            solver.add(s0 >= travel0)
            solver.add(s0 >= friends[i]['start_avail'])
            e0 = s0 + friends[i]['duration']
            solver.add(e0 <= friends[i]['end_avail'])
            
            # Constraints for the second meeting (friend j)
            travel1 = travel_times[friends[i]['location']][friends[j]['location']]
            solver.add(s1 >= e0 + travel1)
            solver.add(s1 >= friends[j]['start_avail'])
            e1 = s1 + friends[j]['duration']
            solver.add(e1 <= friends[j]['end_avail'])
            
            if solver.check() == sat:
                m = solver.model()
                s0_val = m[s0].as_long()
                s1_val = m[s1].as_long()
                
                meeting0 = {
                    "action": "meet",
                    "person": friends[i]['name'],
                    "start_time": minutes_to_time_str(s0_val),
                    "end_time": minutes_to_time_str(s0_val + friends[i]['duration'])
                }
                meeting1 = {
                    "action": "meet",
                    "person": friends[j]['name'],
                    "start_time": minutes_to_time_str(s1_val),
                    "end_time": minutes_to_time_str(s1_val + friends[j]['duration'])
                }
                itinerary = [meeting0, meeting1]
                found = True
                break
        if found:
            break
    if found:
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # Try to schedule one meeting
    for idx in range(3):
        s = Int(f's_{idx}')
        solver = Solver()
        travel0 = travel_times['FW'][friends[idx]['location']]
        solver.add(s >= travel0)
        solver.add(s >= friends[idx]['start_avail'])
        e = s + friends[idx]['duration']
        solver.add(e <= friends[idx]['end_avail'])
        
        if solver.check() == sat:
            m = solver.model()
            s_val = m[s].as_long()
            meeting = {
                "action": "meet",
                "person": friends[idx]['name'],
                "start_time": minutes_to_time_str(s_val),
                "end_time": minutes_to_time_str(s_val + friends[idx]['duration'])
            }
            itinerary = [meeting]
            found = True
            break
    
    if found:
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()