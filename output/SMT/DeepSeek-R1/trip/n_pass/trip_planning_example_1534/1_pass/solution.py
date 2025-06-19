from z3 import *
import json

def main():
    # City indices for clarity
    cities = ["Amsterdam", "Warsaw", "Venice", "Vilnius", "Florence", "Tallinn"]
    lengths = {
        "Amsterdam": 2,
        "Warsaw": 4,
        "Venice": 3,
        "Vilnius": 3,
        "Florence": 5,
        "Tallinn": 2
    }
    direct_flights = {
        "Barcelona": ["Amsterdam", "Warsaw", "Florence", "Venice", "Tallinn"],
        "Amsterdam": ["Warsaw", "Vilnius", "Hamburg", "Venice", "Tallinn", "Florence"],
        "Warsaw": ["Venice", "Vilnius", "Hamburg", "Tallinn"],
        "Venice": ["Hamburg", "Warsaw"],
        "Vilnius": ["Warsaw"],
        "Florence": ["Amsterdam"],
        "Tallinn": ["Vilnius", "Warsaw"]
    }
    directed_flights = {
        "Tallinn": ["Vilnius"]
    }

    s = Solver()
    start_vars = {city: Int(f'start_{city}') for city in cities}
    order = [Int(f'order_{i}') for i in range(6)]
    city_index = {city: idx for idx, city in enumerate(cities)}
    idx_city = {idx: city for idx, city in enumerate(cities)}

    # Ensure order is a permutation of 0 to 5
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 0, o < 6)
    
    # First city must be reachable from Barcelona
    first_city = idx_city[order[0]]
    s.add(Or(*[start_vars[first_city] == 7]))
    s.add(first_city in direct_flights["Barcelona"])
    
    # Last city must have a direct flight to Hamburg
    last_city = idx_city[order[5]]
    s.add(last_city in direct_flights["Hamburg"])
    
    # Start day constraints
    for city in cities:
        s.add(start_vars[city] >= 7, start_vars[city] <= 19 - lengths[city] + 1)
    
    # Sequence constraints
    for i in range(5):
        city_i = idx_city[order[i]]
        city_j = idx_city[order[i+1]]
        end_i = start_vars[city_i] + lengths[city_i] - 1
        s.add(start_vars[city_j] == end_i)
        # Flight constraint
        if city_i in directed_flights and city_j in directed_flights[city_i]:
            pass
        else:
            s.add(Or(
                city_j in direct_flights.get(city_i, []),
                city_i in direct_flights.get(city_j, [])
            ))
    
    # Tallinn must include day 11 or 12
    s.add(Or(
        And(start_vars["Tallinn"] <= 11, start_vars["Tallinn"] + lengths["Tallinn"] - 1 >= 11),
        And(start_vars["Tallinn"] <= 12, start_vars["Tallinn"] + lengths["Tallinn"] - 1 >= 12)
    ))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        start_days = {}
        for city in cities:
            start_days[city] = model.evaluate(start_vars[city]).as_long()
        
        # Determine the sequence
        seq_order = [model.evaluate(order[i]).as_long() for i in range(6)]
        seq_cities = [idx_city[idx] for idx in seq_order]
        
        # Generate itinerary
        itinerary = []
        # Fixed parts
        itinerary.append({"day_range": "Day 1-2", "place": "Paris"})
        itinerary.append({"day_range": "Day 1", "place": "Paris"})
        itinerary.append({"day_range": "Day 2", "place": "Paris"})
        itinerary.append({"day_range": "Day 2", "place": "Barcelona"})
        itinerary.append({"day_range": "Day 2-6", "place": "Barcelona"})
        for day in range(3, 7):
            itinerary.append({"day_range": f"Day {day}", "place": "Barcelona"})
        
        # Cities from day 7 to 19
        # First city: flight from Barcelona to first_city on day 7
        first_city = seq_cities[0]
        itinerary.append({"day_range": f"Day 7", "place": "Barcelona"})
        itinerary.append({"day_range": f"Day 7", "place": first_city})
        start_day = start_days[first_city]
        end_day = start_day + lengths[first_city] - 1
        if lengths[first_city] > 1:
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": first_city})
        for day in range(start_day, end_day + 1):
            itinerary.append({"day_range": f"Day {day}", "place": first_city})
        
        # Subsequent cities
        for i in range(1, 6):
            city = seq_cities[i]
            prev_city = seq_cities[i-1]
            start_day = start_days[city]
            end_day = start_day + lengths[city] - 1
            # Flight from previous city to current city
            itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
            itinerary.append({"day_range": f"Day {start_day}", "place": city})
            if lengths[city] > 1:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            for day in range(start_day, end_day + 1):
                itinerary.append({"day_range": f"Day {day}", "place": city})
        
        # Flight from last city to Hamburg
        last_city = seq_cities[5]
        last_end = start_days[last_city] + lengths[last_city] - 1
        itinerary.append({"day_range": f"Day {last_end}", "place": last_city})
        itinerary.append({"day_range": f"Day {last_end}", "place": "Hamburg"})
        # Hamburg and Salzburg
        itinerary.append({"day_range": "Day 19-22", "place": "Hamburg"})
        for day in range(19, 23):
            itinerary.append({"day_range": f"Day {day}", "place": "Hamburg"})
        itinerary.append({"day_range": "Day 22", "place": "Hamburg"})
        itinerary.append({"day_range": "Day 22", "place": "Salzburg"})
        itinerary.append({"day_range": "Day 22-25", "place": "Salzburg"})
        for day in range(22, 26):
            itinerary.append({"day_range": f"Day {day}", "place": "Salzburg"})
        
        # Output
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()