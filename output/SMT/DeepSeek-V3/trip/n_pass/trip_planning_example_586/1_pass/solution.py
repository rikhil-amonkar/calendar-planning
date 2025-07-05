from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Frankfurt', 'Naples', 'Helsinki', 'Lyon', 'Prague']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }
    
    # Days: 1..12
    days = 12
    s = Solver()
    
    # Variables: day_d is in city_c
    # day_d is represented as an integer (0..4 corresponding to cities)
    vars = [Int(f"day_{d}") for d in range(1, days + 1)]
    for v in vars:
        s.add(And(v >= 0, v <= 4))
    
    # Constraints for days in each city
    # Count occurrences of each city in vars
    for city, idx in city_map.items():
        count = 0
        for v in vars:
            count += If(v == idx, 1, 0)
        if city == 'Frankfurt':
            s.add(count == 3)
        elif city == 'Naples':
            s.add(count == 4)
        elif city == 'Helsinki':
            s.add(count == 4)
        elif city == 'Lyon':
            s.add(count == 3)
        elif city == 'Prague':
            s.add(count == 2)
    
    # Workshop in Prague between day 1 and day 2
    # So, must be in Prague on day 1 or day 2 (or both)
    s.add(Or(vars[0] == city_map['Prague'], vars[1] == city_map['Prague']))
    
    # Annual show in Helsinki from day 2 to day 5 (inclusive)
    # So, days 2, 3, 4, 5 must include Helsinki (but not necessarily all)
    # Wait, the problem says: "You would like to visit Helsinki for 4 days. From day 2 to day 5, there is a annual show you want to attend in Helsinki."
    # So, the 4 days in Helsinki must include days 2-5, but since Helsinki is 4 days, perhaps the 4 days are exactly days 2-5.
    s.add(vars[1] == city_map['Helsinki'])  # day 2
    s.add(vars[2] == city_map['Helsinki'])   # day 3
    s.add(vars[3] == city_map['Helsinki'])   # day 4
    s.add(vars[4] == city_map['Helsinki'])   # day 5
    
    # Flight transitions: consecutive days can only be same city or connected by direct flight
    for d in range(days - 1):
        current_city_idx = vars[d]
        next_city_idx = vars[d + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city_idx == next_city_idx,
            # Check if there's a direct flight
            Or([And(current_city_idx == city_map[c1], next_city_idx == city_map[c2]) 
                for c1 in direct_flights 
                for c2 in direct_flights[c1] if city_map[c2] > city_map[c1]] +
               [And(current_city_idx == city_map[c2], next_city_idx == city_map[c1]) 
                for c1 in direct_flights 
                for c2 in direct_flights[c1] if city_map[c2] > city_map[c1]])
        ))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary_nums = [model.evaluate(vars[d]).as_long() for d in range(days)]
        itinerary_cities = [cities[idx] for idx in itinerary_nums]
        
        # Now, build the itinerary in the required JSON format
        itinerary = []
        current_city = itinerary_cities[0]
        start_day = 1
        
        for day in range(1, days + 1):
            if day == 1:
                continue
            if itinerary_cities[day - 1] != current_city:
                # Flight day
                if start_day != day - 1:
                    itinerary.append({
                        'day_range': f"Day {start_day}-{day - 1}",
                        'place': current_city
                    })
                else:
                    itinerary.append({
                        'day_range': f"Day {start_day}",
                        'place': current_city
                    })
                # Add flight day entries for both cities
                itinerary.append({
                    'day_range': f"Day {day}",
                    'place': current_city
                })
                itinerary.append({
                    'day_range': f"Day {day}",
                    'place': itinerary_cities[day - 1]
                })
                current_city = itinerary_cities[day - 1]
                start_day = day
        # Add the last stay
        if start_day <= days:
            if start_day == days:
                itinerary.append({
                    'day_range': f"Day {start_day}",
                    'place': current_city
                })
            else:
                itinerary.append({
                    'day_range': f"Day {start_day}-{days}",
                    'place': current_city
                })
        
        # Now, adjust for the flight days (since the current approach may not capture overlaps correctly)
        # Let's rebuild itinerary by tracking each day's city and adding flight days when transitions occur.
        itinerary = []
        prev_city = None
        for day in range(1, days + 1):
            current_city = itinerary_cities[day - 1]
            if prev_city is None:
                prev_city = current_city
                start_day = day
            else:
                if current_city != prev_city:
                    # Add the stay in prev_city up to day-1
                    if start_day == day - 1:
                        itinerary.append({
                            'day_range': f"Day {start_day}",
                            'place': prev_city
                        })
                    else:
                        itinerary.append({
                            'day_range': f"Day {start_day}-{day - 1}",
                            'place': prev_city
                        })
                    # Add the flight day entries
                    itinerary.append({
                        'day_range': f"Day {day}",
                        'place': prev_city
                    })
                    itinerary.append({
                        'day_range': f"Day {day}",
                        'place': current_city
                    })
                    prev_city = current_city
                    start_day = day
        # Add the last stay
        if start_day <= days:
            if start_day == days:
                itinerary.append({
                    'day_range': f"Day {start_day}",
                    'place': prev_city
                })
            else:
                itinerary.append({
                    'day_range': f"Day {start_day}-{days}",
                    'place': prev_city
                })
        
        # Now, verify that the itinerary meets the day counts
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            day_range = entry['day_range']
            place = entry['place']
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                days_in_place = end - start + 1
            else:
                days_in_place = 1
            day_counts[place] += days_in_place
        
        # Check if day counts match requirements
        assert day_counts['Frankfurt'] == 3
        assert day_counts['Naples'] == 4
        assert day_counts['Helsinki'] == 4
        assert day_counts['Lyon'] == 3
        assert day_counts['Prague'] == 2
        
        # Check Helsinki show days (2-5)
        helsinki_days = []
        for entry in itinerary:
            day_range = entry['day_range']
            place = entry['place']
            if place == 'Helsinki':
                if '-' in day_range:
                    start, end = map(int, day_range.replace('Day ', '').split('-'))
                    days_in_place = list(range(start, end + 1))
                else:
                    days_in_place = [int(day_range.replace('Day ', ''))]
                helsinki_days.extend(days_in_place)
        # Check that days 2-5 are included in Helsinki days
        assert all(day in helsinki_days for day in [2, 3, 4, 5])
        
        # Check Prague workshop between day 1 and day 2
        prague_days = []
        for entry in itinerary:
            day_range = entry['day_range']
            place = entry['place']
            if place == 'Prague':
                if '-' in day_range:
                    start, end = map(int, day_range.replace('Day ', '').split('-'))
                    days_in_place = list(range(start, end + 1))
                else:
                    days_in_place = [int(day_range.replace('Day ', ''))]
                prague_days.extend(days_in_place)
        assert any(day in [1, 2] for day in prague_days)
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))