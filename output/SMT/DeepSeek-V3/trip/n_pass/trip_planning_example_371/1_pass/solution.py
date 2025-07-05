from z3 import *

def solve_trip_planning():
    cities = ['Vienna', 'Stockholm', 'Nice', 'Split']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    direct_flights = {
        'Vienna': ['Stockholm', 'Nice', 'Split'],
        'Stockholm': ['Vienna', 'Nice', 'Split'],
        'Nice': ['Vienna', 'Stockholm'],
        'Split': ['Vienna', 'Stockholm']
    }
    
    days = 9
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    for day_var in day_vars:
        s.add(day_var >= 0, day_var < len(cities))
    
    s.add(Sum([If(day_vars[i] == city_map['Nice'], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(day_vars[i] == city_map['Stockholm'], 1, 0) for i in range(days)]) == 5)
    s.add(Sum([If(day_vars[i] == city_map['Split'], 1, 0) for i in range(days)]) == 3)
    s.add(Sum([If(day_vars[i] == city_map['Vienna'], 1, 0) for i in range(days)]) == 2)
    
    s.add(day_vars[6] == city_map['Split'])  # day 7
    s.add(day_vars[8] == city_map['Split'])  # day 9
    
    s.add(Or(day_vars[0] == city_map['Vienna'], day_vars[1] == city_map['Vienna']))
    
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        s.add(Implies(current_city != next_city, 
                      Or([And(current_city == city_map[a], next_city == city_map[b]) 
                          for a in direct_flights 
                          for b in direct_flights[a] if a != b])))
    
    if s.check() == sat:
        m = s.model()
        day_assignments = [m.eval(day_vars[i]).as_long() for i in range(days)]
        city_names = {v: k for k, v in city_map.items()}
        assignments = [city_names[day_assignments[i]] for i in range(days)]
        
        itinerary = []
        current_place = assignments[0]
        start_day = 1
        
        for i in range(1, days):
            if assignments[i] != assignments[i-1]:
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {end_day}", "place": assignments[i]})
                current_place = assignments[i]
                start_day = i + 1
        
        if start_day <= days:
            if start_day == days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        # Now, we need to merge consecutive entries for the same day_range and place
        # But flight days should remain separate
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            if i < n - 1 and itinerary[i+1]['day_range'] == current['day_range'] and itinerary[i+1]['place'] != current['place']:
                # Flight day: add both
                merged_itinerary.append(current)
                merged_itinerary.append(itinerary[i+1])
                i += 2
            else:
                merged_itinerary.append(current)
                i += 1
        
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_trip_planning()
import json
print(json.dumps(result, indent=2))