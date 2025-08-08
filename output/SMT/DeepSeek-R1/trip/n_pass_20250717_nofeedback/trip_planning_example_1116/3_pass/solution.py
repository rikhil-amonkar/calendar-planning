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
    for (a, b) in direct_flight_pairs:
        a_const = city_dict[a]
        b_const = city_dict[b]
        allowed_pairs.add((a_const, b_const))
        allowed_pairs.add((b_const, a_const))
    
    E = [Const('E%d' % i, CitySort) for i in range(21)]
    s = Solver()
    
    for d in range(1, 21):
        prev_city = E[d-1]
        curr_city = E[d]
        flight_cond = Or([And(prev_city == a, curr_city == b) for (a, b) in allowed_pairs])
        s.add(If(prev_city != curr_city, flight_cond, True))
    
    total_days = {city: 0 for city in cities}
    for city in cities:
        c = city_dict[city]
        count = 0
        for d in range(1, 21):
            count += If(Or(E[d-1] == c, E[d] == c), 1, 0)
        s.add(count == {
            'Oslo': 2, 'Reykjavik': 5, 'Stockholm': 4, 'Munich': 4,
            'Frankfurt': 4, 'Barcelona': 3, 'Bucharest': 2, 'Split': 3
        }[city])
    
    oslo = city_dict['Oslo']
    s.add(Or(E[15] == oslo, E[16] == oslo))
    s.add(Or(E[16] == oslo, E[17] == oslo))
    
    reykjavik = city_dict['Reykjavik']
    s.add(Or([Or(E[d-1] == reykjavik, E[d] == reykjavik) for d in range(9, 14)]))
    
    munich = city_dict['Munich']
    for d in range(13, 17):
        s.add(Or(E[d-1] == munich, E[d] == munich))
    
    frankfurt = city_dict['Frankfurt']
    for d in range(17, 21):
        s.add(Or(E[d-1] == frankfurt, E[d] == frankfurt))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        end_day = 1
        
        for d in range(1, 21):
            c_val = model[E[d]]
            place = [name for name, const in city_dict.items() if model.evaluate(const) == c_val][0]
            
            if d == 1:
                current_city = place
                continue
                
            if place == current_city:
                end_day = d
            else:
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": current_city
                })
                current_city = place
                start_day = d
                end_day = d
        
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": current_city
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()