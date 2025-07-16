from z3 import *
import json

def solve_itinerary():
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", 
              "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    
    direct_flights = {
        "Valencia": ["Frankfurt", "Athens", "Bucharest", "Vienna", "Amsterdam"],
        "Vienna": ["Bucharest", "Riga", "Frankfurt", "Stockholm", "Amsterdam", "Athens", "Reykjavik", "Valencia"],
        "Athens": ["Valencia", "Bucharest", "Riga", "Stockholm", "Frankfurt", "Vienna", "Reykjavik", "Amsterdam"],
        "Riga": ["Frankfurt", "Bucharest", "Vienna", "Amsterdam", "Stockholm", "Athens"],
        "Stockholm": ["Athens", "Vienna", "Amsterdam", "Reykjavik", "Frankfurt", "Riga"],
        "Amsterdam": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Valencia", "Vienna", "Riga", "Athens"],
        "Bucharest": ["Vienna", "Athens", "Amsterdam", "Frankfurt", "Valencia", "Riga"],
        "Frankfurt": ["Valencia", "Riga", "Amsterdam", "Salzburg", "Vienna", "Athens", "Bucharest", "Stockholm", "Reykjavik"],
        "Reykjavik": ["Amsterdam", "Frankfurt", "Athens", "Stockholm", "Vienna"],
        "Salzburg": ["Frankfurt"]
    }
    
    total_days = 29
    
    s = Solver()
    
    day_place = [Int(f"day_{d+1}") for d in range(total_days)]
    
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for d in range(total_days):
        s.add(day_place[d] >= 0, day_place[d] < len(cities))
    
    for d in range(total_days - 1):
        current_city = day_place[d]
        next_city = day_place[d+1]
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_to_int[src], next_city == city_to_int[dest]) 
                for src in cities for dest in direct_flights.get(src, [])])
        ))
    
    def add_stay_constraint(city, start_day, end_day):
        for d in range(start_day - 1, end_day):
            s.add(day_place[d] == city_to_int[city])
    
    add_stay_constraint("Stockholm", 1, 3)
    add_stay_constraint("Valencia", 5, 6)
    add_stay_constraint("Vienna", 6, 10)
    add_stay_constraint("Athens", 14, 18)
    add_stay_constraint("Riga", 18, 20)
    
    city_days = {
        "Frankfurt": 4,
        "Salzburg": 5,
        "Athens": 5,
        "Reykjavik": 5,
        "Bucharest": 3,
        "Valencia": 2,
        "Vienna": 5,
        "Amsterdam": 3,
        "Stockholm": 3,
        "Riga": 3
    }
    
    for city in cities:
        total = 0
        for d in range(total_days):
            total += If(day_place[d] == city_to_int[city], 1, 0)
        s.add(total == city_days[city])
    
    if s.check() == sat:
        m = s.model()
        sequence = [m.evaluate(day_place[d]).as_long() for d in range(total_days)]
        city_sequence = [int_to_city[idx] for idx in sequence]
        
        itinerary = []
        current_city = city_sequence[0]
        start_day = 1
        for day in range(1, total_days + 1):
            if day == total_days or city_sequence[day] != city_sequence[day - 1]:
                end_day = day
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
                if day < total_days:
                    next_city = city_sequence[day]
                    itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                    itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
                start_day = day + 1
                if day < total_days:
                    current_city = city_sequence[day]
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))