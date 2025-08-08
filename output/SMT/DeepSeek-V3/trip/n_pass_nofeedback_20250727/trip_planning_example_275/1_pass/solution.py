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
    
    # Direct flight connections: adjacency list
    connections = {
        Split: [Vilnius, Madrid],
        Vilnius: [Split],
        Madrid: [Split, Santorini],
        Santorini: [Madrid]
    }
    
    # Transition constraints: consecutive days must be the same city or connected
    for i in range(13):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == c1, next_city == c2) 
              for c1 in connections for c2 in connections[c1]]
        ))
    
    # Fixed days in Santorini on days 13 and 14 (indices 12 and 13)
    s.add(days[12] == Santorini)
    s.add(days[13] == Santorini)
    
    # Total days per city constraints
    total_days = {c: 0 for c in cities.values()}
    for c in cities.values():
        total_days[c] = Sum([If(day == c, 1, 0) for day in days])
    
    s.add(total_days[Split] == 5)
    s.add(total_days[Vilnius] == 4)
    s.add(total_days[Santorini] == 2)  # days 13-14 already enforce this
    s.add(total_days[Madrid] == 6)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(14):
            day_num = i + 1
            city_val = m.evaluate(days[i]).as_long()
            city_name = city_names[city_val]
            itinerary.append({"day": day_num, "place": city_name})
        
        # Verify the counts
        counts = {name: 0 for name in city_names.values()}
        for entry in itinerary:
            counts[entry["place"]] += 1
        
        # Verify transitions are valid
        valid = True
        for i in range(13):
            current = itinerary[i]["place"]
            next_ = itinerary[i+1]["place"]
            if current != next_:
                # Check if there's a direct flight
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
                else:
                    valid = False
        if not valid:
            print("Invalid transitions in itinerary")
        
        # Check counts
        expected_counts = {
            "Split": 5,
            "Vilnius": 4,
            "Santorini": 2,
            "Madrid": 6
        }
        for city, cnt in expected_counts.items():
            if counts[city] != cnt:
                print(f"Count mismatch for {city}: expected {cnt}, got {counts[city]}")
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))