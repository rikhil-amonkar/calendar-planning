from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ["Paris", "Venice", "Vilnius", "Salzburg", "Amsterdam", 
              "Barcelona", "Hamburg", "Florence", "Tallinn", "Warsaw"]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (corrected)
    direct_flights = {
        "Paris": ["Venice", "Vilnius", "Amsterdam", "Florence", "Hamburg", "Warsaw", "Tallinn", "Barcelona"],
        "Venice": ["Paris", "Warsaw", "Barcelona", "Amsterdam", "Hamburg"],
        "Vilnius": ["Paris", "Amsterdam", "Warsaw", "Tallinn"],
        "Salzburg": ["Hamburg"],
        "Amsterdam": ["Barcelona", "Warsaw", "Vilnius", "Hamburg", "Florence", "Venice", "Tallinn", "Paris"],
        "Barcelona": ["Amsterdam", "Warsaw", "Hamburg", "Florence", "Venice", "Tallinn", "Paris"],
        "Hamburg": ["Amsterdam", "Barcelona", "Paris", "Venice", "Warsaw", "Salzburg"],
        "Florence": ["Barcelona", "Paris", "Amsterdam"],
        "Tallinn": ["Barcelona", "Warsaw", "Vilnius", "Amsterdam", "Paris"],
        "Warsaw": ["Amsterdam", "Barcelona", "Venice", "Vilnius", "Tallinn", "Hamburg", "Paris"],
    }

    # Create solver
    s = Solver()

    # Variables: city each day (1..25)
    day_city = [Int(f'day_{day}') for day in range(1, 26)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))

    # Helper function to count days in a city
    def days_in_city(city):
        return Sum([If(day_city[d] == city_index[city], 1, 0) for d in range(25)])

    # Fixed events first
    # Paris workshop days 1-2
    s.add(day_city[0] == city_index["Paris"])
    s.add(day_city[1] == city_index["Paris"])

    # Barcelona with friends days 2-6
    for day in range(1, 6):
        s.add(day_city[day] == city_index["Barcelona"])

    # Tallinn meet friend days 11-12
    s.add(day_city[10] == city_index["Tallinn"])
    s.add(day_city[11] == city_index["Tallinn"])

    # Hamburg conference days 19-22
    for day in range(18, 22):
        s.add(day_city[day] == city_index["Hamburg"])

    # Salzburg wedding days 22-25
    for day in range(21, 25):
        s.add(day_city[day] == city_index["Salzburg"])

    # Flight constraints
    for day in range(24):
        current = day_city[day]
        next_day = day_city[day + 1]
        s.add(Implies(current != next_day, 
                     Or([next_day == city_index[dest] for dest in direct_flights[cities[current.as_long()]])))

    # Total days requirements
    s.add(days_in_city("Paris") == 2)
    s.add(days_in_city("Venice") == 3)
    s.add(days_in_city("Vilnius") == 3)
    s.add(days_in_city("Salzburg") == 4)
    s.add(days_in_city("Amsterdam") == 2)
    s.add(days_in_city("Barcelona") == 5)
    s.add(days_in_city("Hamburg") == 4)
    s.add(days_in_city("Florence") == 5)
    s.add(days_in_city("Tallinn") == 2)
    s.add(days_in_city("Warsaw") == 4)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        current = None
        start_day = 1
        
        for day in range(25):
            city_idx = model.evaluate(day_city[day]).as_long()
            city = cities[city_idx]
            
            if city != current:
                if current is not None:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current})
                itinerary.append({"day_range": f"Day {day+1}", "place": city})
                start_day = day + 1
                current = city
                
        itinerary.append({"day_range": f"Day {start_day}-25", "place": current})

        # Process flight days
        final_itinerary = []
        i = 0
        while i < len(itinerary):
            entry = itinerary[i]
            if i+1 < len(itinerary) and itinerary[i+1]['day_range'].startswith(entry['day_range'].split('-')[0] + '-'):
                day = int(entry['day_range'].split('-')[0][4:])
                final_itinerary.append({"day_range": f"Day {day}", "place": entry['place']})
                final_itinerary.append({"day_range": f"Day {day}", "place": itinerary[i+1]['place']})
                i += 1
            else:
                final_itinerary.append(entry)
            i += 1

        return {"itinerary": final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)