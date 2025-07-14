from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    city_list = list(cities.keys())
    
    # Direct flights (undirected)
    direct_flights = {
        "Istanbul": ["Krakow", "Warsaw", "Riga"],
        "Krakow": ["Istanbul", "Warsaw"],
        "Warsaw": ["Istanbul", "Krakow", "Reykjavik", "Riga"],
        "Riga": ["Istanbul", "Warsaw"],
        "Reykjavik": ["Warsaw"]
    }
    
    total_days = 21
    
    s = Solver()
    
    # Day variables (1-based indexing)
    day_vars = [Int(f"day_{i}") for i in range(1, total_days+1)]
    
    # City to index mapping
    city_idx = {city: i for i, city in enumerate(city_list)}
    
    # Each day must be one of the cities
    for day in day_vars:
        s.add(Or([day == city_idx[city] for city in city_list]))
    
    # Flight transitions
    for i in range(total_days-1):
        current = day_vars[i]
        next_day = day_vars[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == city_idx[c1], next_day == city_idx[c2]) 
              for c1 in city_list for c2 in direct_flights[c1]]
        ))
    
    # Total days in each city
    for city in city_list:
        count = Sum([If(day_vars[i] == city_idx[city], 1, 0) 
                 for i in range(total_days)])
        s.add(count == cities[city])
    
    # Wedding in Istanbul between day 2-7
    s.add(Or([day_vars[i] == city_idx["Istanbul"] for i in range(1, 7)]))
    
    # Meeting in Riga on day 1 or 2
    s.add(Or(day_vars[0] == city_idx["Riga"], day_vars[1] == city_idx["Riga"]))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Generate day sequence
        seq = []
        for i in range(total_days):
            city_idx_val = model.evaluate(day_vars[i]).as_long()
            seq.append((i+1, city_list[city_idx_val]))  # (day, city)
        
        # Process into itinerary format
        i = 0
        while i < total_days:
            start_day = i+1
            current_city = seq[i][1]
            j = i
            while j < total_days and seq[j][1] == current_city:
                j += 1
            end_day = j  # days are 1-based
            
            # Add stay period
            if start_day == end_day:
                day_str = f"Day {start_day}"
            else:
                day_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_str, "place": current_city})
            
            # Add flight day if changing cities
            if j < total_days:
                next_city = seq[j][1]
                itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
            
            i = j
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))