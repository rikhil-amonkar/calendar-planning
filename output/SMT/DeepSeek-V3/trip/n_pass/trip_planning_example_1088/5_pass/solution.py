from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ["Reykjavik", "Stuttgart", "Oslo", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva", "Reykjavik"],
        "Stuttgart": ["Porto", "Reykjavik", "Stockholm", "Split"],
        "Oslo": ["Stockholm", "Split", "Geneva", "Porto", "Tallinn", "Reykjavik"],
        "Split": ["Stuttgart", "Oslo", "Stockholm", "Geneva"],
        "Geneva": ["Porto", "Oslo", "Stockholm", "Split"],
        "Porto": ["Stuttgart", "Oslo", "Geneva"],
        "Tallinn": ["Oslo", "Reykjavik"]
    }

    # Create solver
    s = Solver()

    # Day variables (1-21)
    day_city = [Int(f"day_{d}") for d in range(1, 22)]

    # Each day must be one of the cities
    for d in range(21):
        s.add(And(day_city[d] >= 0, day_city[d] < 8))

    # Fixed events:
    # Days 1-2 in Reykjavik
    s.add(day_city[0] == city_idx["Reykjavik"])
    s.add(day_city[1] == city_idx["Reykjavik"])

    # Days 19-21 in Porto
    s.add(day_city[18] == city_idx["Porto"])
    s.add(day_city[19] == city_idx["Porto"])
    s.add(day_city[20] == city_idx["Porto"])

    # Meet in Stockholm between days 2-4
    s.add(Or(day_city[1] == city_idx["Stockholm"],
             day_city[2] == city_idx["Stockholm"],
             day_city[3] == city_idx["Stockholm"]))

    # Flight constraints between consecutive days
    for d in range(20):
        current = day_city[d]
        next_day = day_city[d+1]
        same_city = (current == next_day)
        
        # Get all possible flight connections
        flight_options = []
        for city in direct_flights:
            for neighbor in direct_flights[city]:
                flight_options.append(And(current == city_idx[city], 
                                        next_day == city_idx[neighbor]))
                
        s.add(Or(same_city, Or(flight_options)))

    # Duration constraints
    def count_days(city_name):
        return Sum([If(day_city[d] == city_idx[city_name], 1, 0) for d in range(21)])

    s.add(count_days("Oslo") == 5)
    s.add(count_days("Stuttgart") == 5)
    s.add(count_days("Reykjavik") == 2)
    s.add(count_days("Split") == 3)
    s.add(count_days("Geneva") == 2)
    s.add(count_days("Porto") == 3)
    s.add(count_days("Tallinn") == 5)
    s.add(count_days("Stockholm") == 3)

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(21):
            city_idx = m.evaluate(day_city[d]).as_long()
            itinerary.append({"day": d+1, "city": cities[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found with given constraints"}

result = solve_itinerary()
print(result)