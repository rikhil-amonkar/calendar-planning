from z3 import *
import json

def main():
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    CitySort, city_consts = EnumSort('City', cities)
    city_dict = {name: const for name, const in zip(cities, city_consts)}
    
    direct_flight_pairs = [
        ("Reykjavik", "Munich"), ("Munich", "Frankfurt"), ("Split", "Oslo"),
        ("Reykjavik", "Oslo"), ("Bucharest", "Munich"), ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"), ("Barcelona", "Frankfurt"), ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"), ("Barcelona", "Reykjavik"), ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"), ("Bucharest", "Oslo"), ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"), ("Barcelona", "Oslo"), ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"), ("Split", "Frankfurt"), ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"), ("Munich", "Oslo"), ("Split", "Munich")
    ]
    
    allowed_pairs = set()
    for a, b in direct_flight_pairs:
        a_const = city_dict[a]
        b_const = city_dict[b]
        allowed_pairs.add((a_const, b_const))
        allowed_pairs.add((b_const, a_const))
    
    # Nights 0 to 20 (21 nights)
    N = [Const(f'N{i}', CitySort) for i in range(21)]
    s = Solver()
    
    # Flight constraints between consecutive nights
    for i in range(20):
        same_city = N[i] == N[i+1]
        flight_valid = Or([And(N[i] == a, N[i+1] == b) for (a, b) in allowed_pairs])
        s.add(If(same_city, True, flight_valid))
    
    # Day counts per city (days 1 to 20)
    for city, total in zip(cities, [2, 5, 4, 4, 4, 3, 2, 3]):
        c = city_dict[city]
        count = 0
        for i in range(20):  # Each day is between night i and i+1
            count += If(Or(N[i] == c, N[i+1] == c), 1, 0)
        s.add(count == total)
    
    # Event constraints
    oslo = city_dict['Oslo']
    s.add(Or(N[15] == oslo, N[16] == oslo))  # Day 16
    s.add(Or(N[16] == oslo, N[17] == oslo))  # Day 17
    
    reykjavik = city_dict['Reykjavik']
    for i in range(8, 13):  # Days 9-13 (nights 8-13)
        s.add(Or(N[i] == reykjavik, N[i+1] == reykjavik))
    
    munich = city_dict['Munich']
    for i in range(12, 16):  # Days 13-16 (nights 12-16)
        s.add(Or(N[i] == munich, N[i+1] == munich))
    
    frankfurt = city_dict['Frankfurt']
    for i in range(16, 20):  # Days 17-20 (nights 16-20)
        s.add(Or(N[i] == frankfurt, N[i+1] == frankfurt))
    
    # Solve and create itinerary
    if s.check() == sat:
        model = s.model()
        # Get starting city for each day (night before)
        start_cities = []
        for i in range(20):
            c_val = model[N[i]]
            city_name = [name for name, const in city_dict.items() if model.evaluate(const) == c_val][0]
            start_cities.append(city_name)
        
        # Group consecutive days with same starting city
        itinerary = []
        current_city = start_cities[0]
        start_day = 1
        end_day = 1
        
        for day in range(1, 20):  # day index 1 to 19 (0-based)
            if start_cities[day] == current_city:
                end_day = day + 1
            else:
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": current_city})
                current_city = start_cities[day]
                start_day = day + 1
                end_day = day + 1
        
        # Add last group
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()