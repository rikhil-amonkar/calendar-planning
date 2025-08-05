from z3 import *
import itertools

def main():
    travel_times = {
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Embarcadero'): 19,
        ('Mission District', 'Financial District'): 17,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Financial District'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Embarcadero'): 4
    }
    
    friends = {
        'Joseph': {'location': "Fisherman's Wharf", 'window_start': 8*60, 'window_end': 17*60+30, 'min_duration': 90},
        'Jeffrey': {'location': 'Bayview', 'window_start': 17*60+30, 'window_end': 21*60+30, 'min_duration': 60},
        'Kevin': {'location': 'Mission District', 'window_start': 11*60+15, 'window_end': 15*60+15, 'min_duration': 30},
        'Barbara': {'location': 'Financial District', 'window_start': 10*60+30, 'window_end': 16*60+30, 'min_duration': 15}
    }
    
    perm_list = list(itertools.permutations(['Joseph', 'Kevin', 'Barbara']))
    solution_found = False
    itinerary = []
    
    for perm in perm_list:
        loc0 = 'Golden Gate Park'
        loc1 = friends[perm[0]]['location']
        loc2 = friends[perm[1]]['location']
        loc3 = friends[perm[2]]['location']
        loc4 = friends['Jeffrey']['location']
        
        try:
            t0 = travel_times[(loc0, loc1)]
            t1 = travel_times[(loc1, loc2)]
            t2 = travel_times[(loc2, loc3)]
            t3 = travel_times[(loc3, loc4)]
        except KeyError:
            continue
        
        s1 = Int('s1')
        d1 = Int('d1')
        s2 = Int('s2')
        d2 = Int('d2')
        s3 = Int('s3')
        d3 = Int('d3')
        s4 = Int('s4')
        d4 = Int('d4')
        
        solver = Solver()
        solver.add(s1 == 9*60 + t0)
        solver.add(s2 == s1 + d1 + t1)
        solver.add(s3 == s2 + d2 + t2)
        solver.add(s4 == s3 + d3 + t3)
        
        # Constraints for the first friend in the permutation
        solver.add(s1 >= friends[perm[0]]['window_start'])
        solver.add(s1 + d1 <= friends[perm[0]]['window_end'])
        solver.add(d1 >= friends[perm[0]]['min_duration'])
        
        # Constraints for the second friend
        solver.add(s2 >= friends[perm[1]]['window_start'])
        solver.add(s2 + d2 <= friends[perm[1]]['window_end'])
        solver.add(d2 >= friends[perm[1]]['min_duration'])
        
        # Constraints for the third friend
        solver.add(s3 >= friends[perm[2]]['window_start'])
        solver.add(s3 + d3 <= friends[perm[2]]['window_end'])
        solver.add(d3 >= friends[perm[2]]['min_duration'])
        
        # Constraints for Jeffrey
        solver.add(s4 >= friends['Jeffrey']['window_start'])
        solver.add(s4 + d4 <= friends['Jeffrey']['window_end'])
        solver.add(d4 >= friends['Jeffrey']['min_duration'])
        
        if solver.check() == sat:
            model = solver.model()
            s1_val = model.evaluate(s1).as_long()
            d1_val = model.evaluate(d1).as_long()
            s2_val = model.evaluate(s2).as_long()
            d2_val = model.evaluate(d2).as_long()
            s3_val = model.evaluate(s3).as_long()
            d3_val = model.evaluate(d3).as_long()
            s4_val = model.evaluate(s4).as_long()
            d4_val = model.evaluate(d4).as_long()
            
            def format_time(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"
            
            itinerary = [
                {"action": "meet", "person": perm[0], "start_time": format_time(s1_val), "end_time": format_time(s1_val + d1_val)},
                {"action": "meet", "person": perm[1], "start_time": format_time(s2_val), "end_time": format_time(s2_val + d2_val)},
                {"action": "meet", "person": perm[2], "start_time": format_time(s3_val), "end_time": format_time(s3_val + d3_val)},
                {"action": "meet", "person": "Jeffrey", "start_time": format_time(s4_val), "end_time": format_time(s4_val + d4_val)}
            ]
            solution_found = True
            break
    
    if not solution_found:
        itinerary = []
    
    result = {"itinerary": itinerary}
    print(f"SOLUTION: {result}")

if __name__ == "__main__":
    main()