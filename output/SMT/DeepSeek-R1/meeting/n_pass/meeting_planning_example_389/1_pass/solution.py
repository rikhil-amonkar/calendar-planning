import json
import itertools
from z3 import *

def main():
    friends = [
        {"name": "Sarah", "loc": "FW", "start_avail": 345, "end_avail": 510, "dur": 105},
        {"name": "Mary", "loc": "RD", "start_avail": 240, "end_avail": 615, "dur": 75},
        {"name": "Helen", "loc": "MS", "start_avail": 765, "end_avail": 810, "dur": 30},
        {"name": "Thomas", "loc": "BV", "start_avail": 375, "end_avail": 585, "dur": 120}
    ]
    
    travel = {
        "HA": {"FW": 23, "RD": 10, "MS": 11, "BV": 18},
        "FW": {"HA": 22, "RD": 18, "MS": 22, "BV": 26},
        "RD": {"HA": 10, "FW": 18, "MS": 20, "BV": 26},
        "MS": {"HA": 12, "FW": 22, "RD": 20, "BV": 15},
        "BV": {"HA": 19, "FW": 25, "RD": 25, "MS": 13}
    }
    
    n = len(friends)
    found = False
    solution_itinerary = []
    
    for k in range(n, 0, -1):
        for subset in itertools.combinations(friends, k):
            for perm in itertools.permutations(subset):
                solver = Solver()
                start_vars = [Int(f's_{i}') for i in range(k)]
                
                # First meeting: start time >= travel time from HA to first location
                loc0 = perm[0]['loc']
                solver.add(start_vars[0] >= travel['HA'][loc0])
                
                # Chain constraints for subsequent meetings
                for i in range(1, k):
                    prev_loc = perm[i-1]['loc']
                    curr_loc = perm[i]['loc']
                    tt = travel[prev_loc][curr_loc]
                    solver.add(start_vars[i] >= start_vars[i-1] + perm[i-1]['dur'] + tt)
                
                # Availability constraints for each meeting
                for i in range(k):
                    f = perm[i]
                    solver.add(start_vars[i] >= f['start_avail'])
                    solver.add(start_vars[i] + f['dur'] <= f['end_avail'])
                
                if solver.check() == sat:
                    m = solver.model()
                    starts = [m.eval(s).as_long() for s in start_vars]
                    itinerary = []
                    for i in range(k):
                        total_minutes = starts[i]
                        base_hour = 9
                        total_hours = base_hour + total_minutes // 60
                        hours = total_hours
                        minutes = total_minutes % 60
                        start_time = f"{hours:02d}:{minutes:02d}"
                        
                        end_time_minutes = starts[i] + perm[i]['dur']
                        end_hours = base_hour + end_time_minutes // 60
                        end_minutes = end_time_minutes % 60
                        end_time = f"{end_hours:02d}:{end_minutes:02d}"
                        
                        itinerary.append({
                            "action": "meet",
                            "person": perm[i]['name'],
                            "start_time": start_time,
                            "end_time": end_time
                        })
                    
                    solution_itinerary = itinerary
                    found = True
                    break
            if found:
                break
        if found:
            break
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": solution_itinerary}))

if __name__ == "__main__":
    main()