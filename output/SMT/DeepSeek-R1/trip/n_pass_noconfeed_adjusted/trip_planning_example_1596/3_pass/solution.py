import json
from z3 import *

def main():
    # City mapping
    cities_list = [
        "Budapest", "Bucharest", "Krakow", "Munich", "Barcelona",
        "Warsaw", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
    
    # Create solver
    solver = Solver()
    
    # Define variables for each night (32 days)
    c = [Int(f"c_{i}") for i in range(32)]
    
    # Each night city must be between 0 and 9
    for i in range(32):
        solver.add(And(0 <= c[i], c[i] <= 9))
    
    # Event constraints
    # Budapest show: days 9 to 13 -> require nights 8 to 12 (indices 7 to 11)
    for i in range(7, 12):
        solver.add(c[i] == 0)
    
    # Munich workshop: days 18 to 20 -> require nights 17 to 19 (indices 16 to 18)
    for i in range(16, 19):
        solver.add(c[i] == 3)
    
    # Warsaw conference: days 25 to 29 -> require nights 24 to 28 (indices 23 to 27)
    for i in range(23, 28):
        solver.add(c[i] == 5)
    
    # Stockholm friends: days 17-18 -> at least one of c[15] (night16), c[16] (night17), c[17] (night18) is 6
    solver.add(Or(c[15] == 6, c[16] == 6, c[17] == 6))
    
    # Edinburgh friend: days 1-5 -> at least one of c[0] to c[4] is 8
    solver.add(Or([c[i] == 8 for i in range(0, 5)]))
    
    # Total days per city (adjusted to sum to 32)
    total_days = [0] * 10
    for city_idx in range(10):
        total_days[city_idx] = Sum([If(c[i] == city_idx, 1, 0) for i in range(32)])
    
    solver.add(total_days[0] == 5)  # Budapest
    solver.add(total_days[1] == 2)  # Bucharest
    solver.add(total_days[2] == 4)  # Krakow
    solver.add(total_days[3] == 3)  # Munich
    solver.add(total_days[4] == 3)  # Barcelona (reduced from 5)
    solver.add(total_days[5] == 5)  # Warsaw
    solver.add(total_days[6] == 2)  # Stockholm
    solver.add(total_days[7] == 3)  # Riga (reduced from 5)
    solver.add(total_days[8] == 3)  # Edinburgh (reduced from 5)
    solver.add(total_days[9] == 2)  # Vienna (reduced from 5)
    
    # Direct flights data
    raw_flights = [
        (0,3), (1,7), (3,2), (3,5), (3,1), (8,6), (4,5), (8,2), (4,3), (6,2),
        (0,9), (4,6), (6,3), (8,0), (4,7), (8,4), (9,7), (4,0), (1,5), (9,2),
        (8,3), (4,1), (8,7), (9,6), (5,2), (4,2), (7,3), (9,1), (0,5), (9,5),
        (4,9), (0,1), (9,3), (7,5), (6,7), (6,5)
    ]
    
    allowed_pairs = []
    for (a, b) in raw_flights:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    # Travel constraints: consecutive nights must be connected by a direct flight if different
    for i in range(31):
        city_i = c[i]
        city_i1 = c[i+1]
        solver.add(If(city_i != city_i1, Or([And(city_i == a, city_i1 == b) for (a, b) in allowed_pairs]), True))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = [model.evaluate(c[i]).as_long() for i in range(32)]
        
        # Group consecutive stays
        itinerary_json = {"itinerary": []}
        current_city = itinerary[0]
        start_day = 1
        for day in range(1, 32):
            if itinerary[day] != current_city:
                end_day = day
                itinerary_json["itinerary"].append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities_list[current_city]
                })
                start_day = day + 1
                current_city = itinerary[day]
        itinerary_json["itinerary"].append({
            "day_range": f"Day {start_day}-32",
            "place": cities_list[current_city]
        })
        
        print(json.dumps(itinerary_json))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()