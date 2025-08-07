from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Vienna', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Barcelona', 'Stockholm']
    
    # Direct flights (bidirectional)
    direct_flights = {
        'Paris': ['Edinburgh', 'Riga', 'Krakow', 'Hamburg', 'Stockholm', 'Barcelona', 'Vienna'],
        'Vienna': ['Stockholm', 'Hamburg', 'Krakow', 'Barcelona', 'Paris', 'Riga'],
        'Edinburgh': ['Paris', 'Stockholm', 'Riga', 'Barcelona', 'Krakow', 'Hamburg'],
        'Krakow': ['Barcelona', 'Stockholm', 'Edinburgh', 'Paris', 'Vienna'],
        'Riga': ['Barcelona', 'Paris', 'Stockholm', 'Edinburgh', 'Hamburg', 'Vienna'],
        'Hamburg': ['Stockholm', 'Vienna', 'Paris', 'Barcelona', 'Edinburgh', 'Riga'],
        'Barcelona': ['Riga', 'Krakow', 'Hamburg', 'Stockholm', 'Edinburgh', 'Paris', 'Vienna'],
        'Stockholm': ['Hamburg', 'Vienna', 'Edinburgh', 'Krakow', 'Barcelona', 'Paris', 'Riga']
    }
    
    s = Solver()
    
    # Day variables (0-based)
    days = [Int(f'day_{i}') for i in range(16)]
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for day in days:
        s.add(day >= 0, day < 8)
    
    # Fixed events
    s.add(days[0] == city_to_num['Paris'])  # Day 1
    s.add(days[1] == city_to_num['Paris'])  # Day 2
    s.add(days[9] == city_to_num['Hamburg'])  # Day 10
    s.add(days[10] == city_to_num['Hamburg'])  # Day 11
    s.add(Or([days[i] == city_to_num['Edinburgh'] for i in range(11, 15)]))  # Days 12-15
    s.add(days[14] == city_to_num['Stockholm'])  # Day 15
    s.add(days[15] == city_to_num['Stockholm'])  # Day 16
    
    # Count days in each city
    def count_days(city_num):
        return Sum([If(day == city_num, 1, 0) for day in days])
    
    required_days = {
        'Vienna': 4,
        'Barcelona': 2,
        'Edinburgh': 4,  # Includes meeting days
        'Krakow': 3,
        'Riga': 4,
        'Hamburg': 2,    # Conference days
        'Paris': 2,      # Wedding days
        'Stockholm': 2    # Relative visit
    }
    
    for city, num in required_days.items():
        s.add(count_days(city_to_num[city]) == num)
    
    # Flight constraints
    for i in range(15):
        current = days[i]
        next_city = days[i+1]
        s.add(Or(
            current == next_city,
            Or([And(current == city_to_num[city], next_city == city_to_num[dest]) 
                for city in cities for dest in direct_flights[city]])
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            city_num = model.evaluate(days[i]).as_long()
            itinerary.append({"day": i+1, "place": num_to_city[city_num]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry["place"]] += 1
        for city, req in required_days.items():
            assert counts[city] == req, f"{city} count mismatch"
        
        # Verify flights
        for i in range(15):
            curr = itinerary[i]["place"]
            next_p = itinerary[i+1]["place"]
            if curr != next_p:
                assert next_p in direct_flights[curr], f"No flight {curr}->{next_p}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))