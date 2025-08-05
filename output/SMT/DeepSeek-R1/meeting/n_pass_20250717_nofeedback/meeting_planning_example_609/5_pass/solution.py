from z3 import *
import itertools
import json

def main():
    # Corrected travel times with asymmetric distances
    travel_times = {
        'Chinatown': {'Mission District': 18, 'Alamo Square': 17, 'Pacific Heights': 10, 'Union Square': 7, 'Golden Gate Park': 23, 'Sunset District': 29, 'Presidio': 19},
        'Mission District': {'Chinatown': 16, 'Alamo Square': 10, 'Pacific Heights': 16, 'Union Square': 15, 'Golden Gate Park': 17, 'Sunset District': 24, 'Presidio': 25},
        'Alamo Square': {'Chinatown': 17, 'Mission District': 10, 'Pacific Heights': 10, 'Union Square': 14, 'Golden Gate Park': 9, 'Sunset District': 16, 'Presidio': 18},
        'Pacific Heights': {'Chinatown': 11, 'Mission District': 15, 'Alamo Square': 10, 'Union Square': 12, 'Golden Gate Park': 15, 'Sunset District': 21, 'Presidio': 11},
        'Union Square': {'Chinatown': 7, 'Mission District': 14, 'Alamo Square': 15, 'Pacific Heights': 15, 'Golden Gate Park': 22, 'Sunset District': 26, 'Presidio': 24},
        'Golden Gate Park': {'Chinatown': 23, 'Mission District': 17, 'Alamo Square': 9, 'Pacific Heights': 16, 'Union Square': 22, 'Sunset District': 10, 'Presidio': 11},
        'Sunset District': {'Chinatown': 30, 'Mission District': 24, 'Alamo Square': 17, 'Pacific Heights': 21, 'Union Square': 30, 'Golden Gate Park': 10, 'Presidio': 16},
        'Presidio': {'Chinatown': 21, 'Mission District': 26, 'Alamo Square': 18, 'Pacific Heights': 11, 'Union Square': 22, 'Golden Gate Park': 12, 'Sunset District': 15}
    }
    
    # Friend details
    person_location = {
        'David': 'Mission District',
        'Kenneth': 'Alamo Square',
        'John': 'Pacific Heights',
        'Charles': 'Union Square',
        'Deborah': 'Golden Gate Park',
        'Karen': 'Sunset District',
        'Carol': 'Presidio'
    }
    
    # Availability windows in minutes from midnight
    person_window = {
        'David': (8*60, 19*60+45),   # 8:00 AM to 7:45 PM
        'Kenneth': (14*60, 19*60+45), # 2:00 PM to 7:45 PM
        'John': (17*60, 20*60),       # 5:00 PM to 8:00 PM
        'Charles': (21*60+45, 22*60+45), # 9:45 PM to 10:45 PM
        'Deborah': (7*60, 18*60+15),  # 7:00 AM to 6:15 PM
        'Karen': (17*60+45, 21*60+15),# 5:45 PM to 9:15 PM
        'Carol': (8*60+15, 9*60+15)   # 8:15 AM to 9:15 AM
    }
    
    min_duration = {
        'David': 45,
        'Kenneth': 120,
        'John': 15,
        'Charles': 60,
        'Deborah': 90,
        'Karen': 15,
        'Carol': 30
    }
    
    start_location = 'Chinatown'
    start_time = 9 * 60  # 9:00 AM in minutes
    
    persons = list(person_location.keys())
    found_solution = False
    itinerary = []
    
    # Try larger subsets first (maximize meetings)
    for k in range(len(persons), 0, -1):
        for subset in itertools.combinations(persons, k):
            s = Solver()
            positions = {p: Int(f'pos_{p}') for p in subset}
            starts = {p: Int(f'start_{p}') for p in subset}
            ends = {p: Int(f'end_{p}') for p in subset}
            
            # Position constraints
            s.add(Distinct([positions[p] for p in subset]))
            for p in subset:
                s.add(positions[p] >= 0)
                s.add(positions[p] < k)
                s.add(ends[p] == starts[p] + min_duration[p])
                s.add(starts[p] >= person_window[p][0])
                s.add(ends[p] <= person_window[p][1])
                s.add(starts[p] >= 0)
            
            # First meeting must account for travel from start_location
            for p in subset:
                s.add(If(positions[p] == 0,
                         starts[p] >= start_time + travel_times[start_location][person_location[p]],
                         True))
            
            # Consecutive meetings must account for travel time
            for p1 in subset:
                for p2 in subset:
                    if p1 == p2:
                        continue
                    s.add(If(positions[p2] == positions[p1] + 1,
                             starts[p2] >= ends[p1] + travel_times[person_location[p1]][person_location[p2]],
                             True))
            
            # Critical enhancement: Ensure Charles starts immediately when scheduled after Karen
            if 'Karen' in subset and 'Charles' in subset:
                # Force Karen immediately before Charles
                s.add(positions['Charles'] == positions['Karen'] + 1)
                # Charles must start exactly at 21:45 when after Karen
                s.add(starts['Charles'] == 21*60 + 45)
                # Karen must end at 21:15 to allow travel time
                s.add(ends['Karen'] == 21*60 + 15)
            
            # Check for feasible schedule
            if s.check() == sat:
                m = s.model()
                schedule = []
                for p in subset:
                    pos_val = m.evaluate(positions[p]).as_long()
                    start_val = m.evaluate(starts[p]).as_long()
                    end_val = m.evaluate(ends[p]).as_long()
                    schedule.append((pos_val, p, start_val, end_val))
                schedule.sort(key=lambda x: x[0])
                
                # Format itinerary
                itinerary = []
                for _, p, start_val, end_val in schedule:
                    start_str = f"{start_val // 60:02d}:{start_val % 60:02d}"
                    end_str = f"{end_val // 60:02d}:{end_val % 60:02d}"
                    itinerary.append({"action": "meet", "person": p, "start_time": start_str, "end_time": end_str})
                
                found_solution = True
                break
        if found_solution:
            break
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == '__main__':
    main()