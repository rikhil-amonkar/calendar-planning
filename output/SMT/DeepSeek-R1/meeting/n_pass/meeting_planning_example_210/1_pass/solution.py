from z3 import *
import json

def main():
    # Travel times between locations (in minutes)
    travel_times = {
        ('FW', 'P'): 17,   # Fisherman's Wharf to Presidio
        ('FW', 'R'): 18,   # Fisherman's Wharf to Richmond District
        ('FW', 'FD'): 11,  # Fisherman's Wharf to Financial District
        ('P', 'R'): 7,     # Presidio to Richmond District
        ('P', 'FD'): 23,   # Presidio to Financial District
        ('R', 'P'): 7,     # Richmond District to Presidio
        ('R', 'FD'): 22,   # Richmond District to Financial District
        ('FD', 'P'): 22,   # Financial District to Presidio
        ('FD', 'R'): 21,   # Financial District to Richmond District
    }
    
    # Friend details: location, duration, availability (in minutes from 9:00 AM)
    friends = {
        'Emily': {
            'loc': 'P',
            'dur': 105,
            'avail_low': (16*60 + 15) - (9*60),  # 16:15 -> 435 minutes from 9:00
            'avail_high': (21*60) - (9*60) - 105   # 21:00 - 105 minutes = 615 minutes from 9:00
        },
        'Joseph': {
            'loc': 'R',
            'dur': 120,
            'avail_low': (17*60 + 15) - (9*60),    # 17:15 -> 495 minutes from 9:00
            'avail_high': (22*60) - (9*60) - 120   # 22:00 - 120 minutes = 660 minutes from 9:00
        },
        'Melissa': {
            'loc': 'FD',
            'dur': 75,
            'avail_low': (15*60 + 45) - (9*60),    # 15:45 -> 405 minutes from 9:00
            'avail_high': (21*60 + 45) - (9*60) - 75 # 21:45 - 75 minutes = 690 minutes from 9:00
        }
    }
    
    # All permutations of meeting orders
    orders = [
        ['Emily', 'Joseph', 'Melissa'],
        ['Emily', 'Melissa', 'Joseph'],
        ['Joseph', 'Emily', 'Melissa'],
        ['Joseph', 'Melissa', 'Emily'],
        ['Melissa', 'Emily', 'Joseph'],
        ['Melissa', 'Joseph', 'Emily']
    ]
    
    solution_found = False
    itinerary_entries = []
    
    for order in orders:
        s = Solver()
        s1 = Int('s1')
        s2 = Int('s2')
        s3 = Int('s3')
        
        f1 = order[0]
        f2 = order[1]
        f3 = order[2]
        
        loc1 = friends[f1]['loc']
        loc2 = friends[f2]['loc']
        loc3 = friends[f3]['loc']
        
        # Travel from Fisherman's Wharf (FW) to first location
        t0 = travel_times[('FW', loc1)]
        # Travel from first to second location
        t1 = travel_times[(loc1, loc2)]
        # Travel from second to third location
        t2 = travel_times[(loc2, loc3)]
        
        # Constraints for first meeting
        s.add(s1 >= t0)
        s.add(s1 >= friends[f1]['avail_low'])
        s.add(s1 <= friends[f1]['avail_high'])
        e1 = s1 + friends[f1]['dur']
        
        # Constraints for second meeting
        s.add(s2 >= e1 + t1)
        s.add(s2 >= friends[f2]['avail_low'])
        s.add(s2 <= friends[f2]['avail_high'])
        e2 = s2 + friends[f2]['dur']
        
        # Constraints for third meeting
        s.add(s3 >= e2 + t2)
        s.add(s3 >= friends[f3]['avail_low'])
        s.add(s3 <= friends[f3]['avail_high'])
        
        if s.check() == sat:
            model = s.model()
            start1 = model[s1].as_long()
            end1 = start1 + friends[f1]['dur']
            start2 = model[s2].as_long()
            end2 = start2 + friends[f2]['dur']
            start3 = model[s3].as_long()
            end3 = start3 + friends[f3]['dur']
            
            # Convert minutes to HH:MM format
            def min_to_time(mins):
                total_mins = 9*60 + mins
                h = total_mins // 60
                m = total_mins % 60
                return f"{h:02d}:{m:02d}"
            
            # Create meeting entries
            entries = [
                {"action": "meet", "person": f1, "start_time": min_to_time(start1), "end_time": min_to_time(end1)},
                {"action": "meet", "person": f2, "start_time": min_to_time(start2), "end_time": min_to_time(end2)},
                {"action": "meet", "person": f3, "start_time": min_to_time(start3), "end_time": min_to_time(end3)}
            ]
            itinerary_entries = entries
            solution_found = True
            break
    
    if solution_found:
        result = {"itinerary": itinerary_entries}
        print(json.dumps(result, indent=4))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()