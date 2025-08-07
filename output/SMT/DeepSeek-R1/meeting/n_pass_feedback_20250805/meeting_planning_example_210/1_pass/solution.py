from z3 import *
import json
from itertools import permutations

def main():
    friends = {
        'Emily': {
            'location': 'P',
            'avail_start': (16*60+15) - (9*60),
            'avail_end': (21*60) - (9*60),
            'min_dur': 105
        },
        'Joseph': {
            'location': 'R',
            'avail_start': (17*60+15) - (9*60),
            'avail_end': (22*60) - (9*60),
            'min_dur': 120
        },
        'Melissa': {
            'location': 'F',
            'avail_start': (15*60+45) - (9*60),
            'avail_end': (21*60+45) - (9*60),
            'min_dur': 75
        }
    }
    
    travel_time_dict = {
        ('FW', 'P'): 17,
        ('FW', 'R'): 18,
        ('FW', 'F'): 11,
        ('P', 'R'): 7,
        ('P', 'F'): 23,
        ('R', 'P'): 7,
        ('R', 'F'): 22,
        ('F', 'P'): 22,
        ('F', 'R'): 21
    }
    
    def convert_to_time(minutes):
        total_minutes = minutes
        h = 9 + total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"
    
    found_schedule = False
    schedule = None
    
    # Try to meet all three friends
    orders_three = list(permutations(['Emily', 'Joseph', 'Melissa']))
    for order in orders_three:
        A, B, C = order
        locA = friends[A]['location']
        locB = friends[B]['location']
        locC = friends[C]['location']
        
        s = Solver()
        startA = Int(f'start_{A}')
        startB = Int(f'start_{B}')
        startC = Int(f'start_{C}')
        
        s.add(startA >= travel_time_dict[('FW', locA)])
        s.add(startA >= friends[A]['avail_start'])
        endA = startA + friends[A]['min_dur']
        s.add(endA <= friends[A]['avail_end'])
        
        s.add(startB >= endA + travel_time_dict[(locA, locB)])
        s.add(startB >= friends[B]['avail_start'])
        endB = startB + friends[B]['min_dur']
        s.add(endB <= friends[B]['avail_end'])
        
        s.add(startC >= endB + travel_time_dict[(locB, locC)])
        s.add(startC >= friends[C]['avail_start'])
        endC = startC + friends[C]['min_dur']
        s.add(endC <= friends[C]['avail_end'])
        
        if s.check() == sat:
            m = s.model()
            startA_val = m.eval(startA).as_long()
            startB_val = m.eval(startB).as_long()
            startC_val = m.eval(startC).as_long()
            
            schedule = [
                {"action": "meet", "person": A, 
                 "start_time": convert_to_time(startA_val), 
                 "end_time": convert_to_time(startA_val + friends[A]['min_dur'])},
                {"action": "meet", "person": B, 
                 "start_time": convert_to_time(startB_val), 
                 "end_time": convert_to_time(startB_val + friends[B]['min_dur'])},
                {"action": "meet", "person": C, 
                 "start_time": convert_to_time(startC_val), 
                 "end_time": convert_to_time(startC_val + friends[C]['min_dur'])}
            ]
            found_schedule = True
            break
    
    if not found_schedule:
        skip_list = ['Emily', 'Joseph', 'Melissa']
        for skip in skip_list:
            the_two = [f for f in ['Emily', 'Joseph', 'Melissa'] if f != skip]
            orders_two = list(permutations(the_two))
            for order in orders_two:
                A, B = order
                locA = friends[A]['location']
                locB = friends[B]['location']
                
                s = Solver()
                startA = Int(f'start_{A}')
                startB = Int(f'start_{B}')
                
                s.add(startA >= travel_time_dict[('FW', locA)])
                s.add(startA >= friends[A]['avail_start'])
                endA = startA + friends[A]['min_dur']
                s.add(endA <= friends[A]['avail_end'])
                
                s.add(startB >= endA + travel_time_dict[(locA, locB)])
                s.add(startB >= friends[B]['avail_start'])
                endB = startB + friends[B]['min_dur']
                s.add(endB <= friends[B]['avail_end'])
                
                if s.check() == sat:
                    m = s.model()
                    startA_val = m.eval(startA).as_long()
                    startB_val = m.eval(startB).as_long()
                    
                    schedule = [
                        {"action": "meet", "person": A, 
                         "start_time": convert_to_time(startA_val), 
                         "end_time": convert_to_time(startA_val + friends[A]['min_dur'])},
                        {"action": "meet", "person": B, 
                         "start_time": convert_to_time(startB_val), 
                         "end_time": convert_to_time(startB_val + friends[B]['min_dur'])}
                    ]
                    found_schedule = True
                    break
            if found_schedule:
                break
    
    if not found_schedule:
        for friend in ['Emily', 'Joseph', 'Melissa']:
            s = Solver()
            startX = Int(f'start_{friend}')
            locX = friends[friend]['location']
            s.add(startX >= travel_time_dict[('FW', locX)])
            s.add(startX >= friends[friend]['avail_start'])
            endX = startX + friends[friend]['min_dur']
            s.add(endX <= friends[friend]['avail_end'])
            
            if s.check() == sat:
                m = s.model()
                startX_val = m.eval(startX).as_long()
                schedule = [
                    {"action": "meet", "person": friend, 
                     "start_time": convert_to_time(startX_val), 
                     "end_time": convert_to_time(startX_val + friends[friend]['min_dur'])}
                ]
                found_schedule = True
                break
    
    print("SOLUTION:")
    result = {"itinerary": schedule}
    print(json.dumps(result))

if __name__ == "__main__":
    main()