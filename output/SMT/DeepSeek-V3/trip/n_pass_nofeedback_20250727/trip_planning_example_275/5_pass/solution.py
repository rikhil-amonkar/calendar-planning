from z3 import *

def solve_itinerary():
    # Cities
    Split, Vilnius, Santorini, Madrid = Ints('Split Vilnius Santorini Madrid')
    cities = {0: Split, 1: Vilnius, 2: Santorini, 3: Madrid}
    city_names = {0: "Split", 1: "Vilnius", 2: "Santorini", 3: "Madrid"}
    
    # Day variables: day[i] is the city on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(14)]
    
    s = Solver()
    
    # Each day must be one of the cities (0 to 3)
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Direct flight connections (bidirectional)
    connections = {
        Split: [Vilnius, Madrid],
        Vilnius: [Split],
        Madrid: [Split, Santorini],
        Santorini: [Madrid]
    }
    
    # Transition constraints
    for i in range(13):
        current = days[i]
        next_ = days[i+1]
        s.add(Or(
            current == next_,  # Stay in same city
            *[And(current == c1, next_ == c2) for c1 in connections for c2 in connections[c1]]
        ))
    
    # Fixed days in Santorini (days 13-14)
    s.add(days[12] == Santorini)
    s.add(days[13] == Santorini)
    
    # Total days per city (accounting for flight days)
    # We'll track days spent in each city
    city_days = {c: 0 for c in cities.values()}
    for c in cities.values():
        city_days[c] = Sum([If(day == c, 1, 0) for day in days])
    
    s.add(city_days[Split] == 5)
    s.add(city_days[Vilnius] == 4)
    s.add(city_days[Santorini] == 2)
    s.add(city_days[Madrid] == 6)
    
    # Additional constraints to ensure feasible transitions
    # Must be in Madrid on day 12 to reach Santorini on day 13
    s.add(days[11] == Madrid)
    
    # Must have at least one transition between cities
    s.add(Or([days[i] != days[i+1] for i in range(13)]))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(14):
            day_num = i + 1
            city_val = m.evaluate(days[i]).as_long()
            city_name = city_names[city_val]
            itinerary.append({"day": day_num, "place": city_name})
        
        # Verify counts
        counts = {name: 0 for name in city_names.values()}
        for entry in itinerary:
            counts[entry["place"]] += 1
        
        # Verify transitions
        valid = True
        for i in range(13):
            current = itinerary[i]["place"]
            next_ = itinerary[i+1]["place"]
            if current != next_:
                if current == "Split":
                    if next_ not in ["Vilnius", "Madrid"]:
                        valid = False
                elif current == "Vilnius":
                    if next_ != "Split":
                        valid = False
                elif current == "Madrid":
                    if next_ not in ["Split", "Santorini"]:
                        valid = False
                elif current == "Santorini":
                    if next_ != "Madrid":
                        valid = False
        
        if not valid:
            return {"error": "Invalid transitions in itinerary"}
        
        # Check counts
        expected_counts = {
            "Split": 5,
            "Vilnius": 4,
            "Santorini": 2,
            "Madrid": 6
        }
        for city, cnt in expected_counts.items():
            if counts[city] != cnt:
                return {"error": f"Count mismatch for {city}: expected {cnt}, got {counts[city]}"}
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))