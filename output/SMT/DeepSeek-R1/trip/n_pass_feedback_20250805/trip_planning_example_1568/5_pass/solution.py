from z3 import *
import json

def main():
    cities = ["Prague", "Brussels", "Riga", "Munich", "Seville", "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"]
    City, city_consts = EnumSort('City', cities)
    Prague, Brussels, Riga, Munich, Seville, Stockholm, Istanbul, Amsterdam, Vienna, Split = city_consts

    direct_flights = [
        ("Riga", "Stockholm"), ("Stockholm", "Brussels"), ("Istanbul", "Munich"), ("Istanbul", "Riga"), 
        ("Prague", "Split"), ("Vienna", "Brussels"), ("Vienna", "Riga"), ("Split", "Stockholm"), 
        ("Munich", "Amsterdam"), ("Split", "Amsterdam"), ("Amsterdam", "Stockholm"), ("Amsterdam", "Riga"), 
        ("Vienna", "Stockholm"), ("Vienna", "Istanbul"), ("Vienna", "Seville"), ("Istanbul", "Amsterdam"), 
        ("Munich", "Brussels"), ("Prague", "Munich"), ("Riga", "Munich"), ("Prague", "Amsterdam"), 
        ("Prague", "Brussels"), ("Prague", "Istanbul"), ("Istanbul", "Stockholm"), ("Vienna", "Prague"), 
        ("Munich", "Split"), ("Vienna", "Amsterdam"), ("Prague", "Stockholm"), ("Brussels", "Seville"), 
        ("Munich", "Stockholm"), ("Istanbul", "Brussels"), ("Amsterdam", "Seville"), ("Vienna", "Split"), 
        ("Munich", "Seville"), ("Riga", "Brussels"), ("Prague", "Riga"), ("Vienna", "Munich")
    ]
    
    flight_set = set()
    for c1_str, c2_str in direct_flights:
        idx1 = cities.index(c1_str)
        idx2 = cities.index(c2_str)
        city1 = city_consts[idx1]
        city2 = city_consts[idx2]
        flight_set.add((city1, city2))
        flight_set.add((city2, city1))
    
    all_pairs = list(flight_set)
    
    loc = [Const(f'loc_{i}', City) for i in range(21)]
    
    s = Solver()
    
    for d in range(1, 21):
        if loc[d-1] != loc[d]:
            valid_flight = False
            for (c1, c2) in all_pairs:
                s.add(Implies(And(loc[d-1] == c1, loc[d] == c2), True))
            s.add(Or([And(loc[d-1] == c1, loc[d] == c2) for (c1, c2) in all_pairs]))
    
    total_days = {}
    for city in city_consts:
        total = 0
        for d in range(1, 21):
            total += If(loc[d] == city, 1, 0)
        total_days[city] = total
    
    s.add(total_days[Vienna] == 5)
    s.add(loc[1] == Vienna)
    s.add(loc[2] == Vienna)
    s.add(loc[3] == Vienna)
    
    s.add(total_days[Prague] == 5)
    s.add(loc[5] == Prague)
    s.add(loc[6] == Prague)
    s.add(loc[7] == Prague)
    s.add(loc[8] == Prague)
    s.add(loc[9] == Prague)
    
    s.add(total_days[Split] == 3)
    s.add(Or(loc[11] == Split, loc[12] == Split, loc[13] == Split))
    
    s.add(total_days[Stockholm] == 2)
    s.add(loc[16] == Stockholm)
    s.add(loc[17] == Stockholm)
    
    s.add(total_days[Riga] == 2)
    s.add(total_days[Brussels] == 2)
    s.add(total_days[Munich] == 2)
    s.add(total_days[Seville] == 3)
    s.add(total_days[Istanbul] == 2)
    s.add(total_days[Amsterdam] == 3)
    
    for city in city_consts:
        for d in range(1, 19):
            s.add(Implies(And(loc[d] == city, loc[d+2] == city), loc[d+1] == city))
    
    if s.check() == sat:
        m = s.model()
        stays = {city: [] for city in city_consts}
        for d in range(1, 21):
            city = m.evaluate(loc[d])
            stays[city].append(d)
        
        blocks = []
        for city, days in stays.items():
            if days:
                first = min(days)
                last = max(days)
                city_name = city.decl().name()
                blocks.append((first, last, city_name))
        
        blocks.sort(key=lambda x: x[0])
        itinerary = []
        for first, last, city_name in blocks:
            itinerary.append({
                'day_range': f'Day {first}-{last}',
                'place': city_name
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()