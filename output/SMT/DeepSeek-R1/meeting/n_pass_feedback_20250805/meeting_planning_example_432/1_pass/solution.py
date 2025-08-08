import itertools
import json
from z3 import Int, Solver, sat

def convert_minutes_to_time(minutes):
    total_hours = minutes // 60
    total_minutes = minutes % 60
    hours = 9 + total_hours
    mins = total_minutes
    return f"{int(hours):02d}:{int(mins):02d}"

def main():
    meetings = [
        {'name': 'Joseph', 'loc': 'FW', 'duration': 90, 'avail_start': -60, 'avail_end': 510},
        {'name': 'Jeffrey', 'loc': 'BV', 'duration': 60, 'avail_start': 510, 'avail_end': 750},
        {'name': 'Kevin', 'loc': 'MD', 'duration': 30, 'avail_start': 135, 'avail_end': 375},
        {'name': 'Barbara', 'loc': 'FD', 'duration': 15, 'avail_start': 90, 'avail_end': 450}
    ]
    
    travel_times = {
        ('GGP','FW'): 24,
        ('GGP','BV'): 23,
        ('GGP','MD'): 17,
        ('GGP','FD'): 26,
        ('FW','BV'): 26,
        ('FW','MD'): 22,
        ('FW','FD'): 11,
        ('BV','FW'): 25,
        ('BV','MD'): 13,
        ('BV','FD'): 19,
        ('MD','FW'): 22,
        ('MD','BV'): 15,
        ('MD','FD'): 17,
        ('FD','FW'): 10,
        ('FD','BV'): 19,
        ('FD','MD'): 17
    }
    
    orders = list(itertools.permutations(range(4)))
    found = False
    itinerary = None

    for order in orders:
        m0 = meetings[order[0]]
        m1 = meetings[order[1]]
        m2 = meetings[order[2]]
        m3 = meetings[order[3]]
        
        s0 = Int('s0')
        s1 = Int('s1')
        s2 = Int('s2')
        s3 = Int('s3')
        
        solver = Solver()
        
        # Constraints for first meeting
        travel0 = travel_times[('GGP', m0['loc'])]
        solver.add(s0 >= travel0)
        solver.add(s0 >= m0['avail_start'])
        solver.add(s0 + m0['duration'] <= m0['avail_end'])
        
        # Constraints for second meeting
        travel1 = travel_times[(m0['loc'], m1['loc'])]
        solver.add(s1 >= s0 + m0['duration'] + travel1)
        solver.add(s1 >= m1['avail_start'])
        solver.add(s1 + m1['duration'] <= m1['avail_end'])
        
        # Constraints for third meeting
        travel2 = travel_times[(m1['loc'], m2['loc'])]
        solver.add(s2 >= s1 + m1['duration'] + travel2)
        solver.add(s2 >= m2['avail_start'])
        solver.add(s2 + m2['duration'] <= m2['avail_end'])
        
        # Constraints for fourth meeting
        travel3 = travel_times[(m2['loc'], m3['loc'])]
        solver.add(s3 >= s2 + m2['duration'] + travel3)
        solver.add(s3 >= m3['avail_start'])
        solver.add(s3 + m3['duration'] <= m3['avail_end'])
        
        if solver.check() == sat:
            model = solver.model()
            s0_val = model.eval(s0).as_long()
            s1_val = model.eval(s1).as_long()
            s2_val = model.eval(s2).as_long()
            s3_val = model.eval(s3).as_long()
            
            meetings_in_order = [
                (m0, s0_val),
                (m1, s1_val),
                (m2, s2_val),
                (m3, s3_val)
            ]
            
            itinerary_list = []
            for meet, start in meetings_in_order:
                end_time = start + meet['duration']
                itinerary_list.append({
                    "action": "meet",
                    "person": meet['name'],
                    "start_time": convert_minutes_to_time(start),
                    "end_time": convert_minutes_to_time(end_time)
                })
            
            itinerary = itinerary_list
            found = True
            break
    
    if not found:
        itinerary = []
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()