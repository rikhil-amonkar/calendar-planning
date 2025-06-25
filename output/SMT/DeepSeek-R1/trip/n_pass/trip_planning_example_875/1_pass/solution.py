from z3 import *

def main():
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    durations = {
        'Stuttgart': 3,
        'Edinburgh': 4,
        'Athens': 4,
        'Split': 2,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 4
    }
    
    edges = [
        ('Krakow', 'Split'),
        ('Split', 'Athens'),
        ('Edinburgh', 'Krakow'),
        ('Venice', 'Stuttgart'),
        ('Krakow', 'Stuttgart'),
        ('Edinburgh', 'Stuttgart'),
        ('Stuttgart', 'Athens'),
        ('Venice', 'Edinburgh'),
        ('Athens', 'Mykonos'),
        ('Venice', 'Athens'),
        ('Stuttgart', 'Split'),
        ('Edinburgh', 'Athens')
    ]
    
    edge_set = set()
    for u, v in edges:
        key = tuple(sorted([u, v]))
        edge_set.add(key)
    
    s = Solver()
    
    pos = {city: Int(f'pos_{city}') for city in cities}
    
    for city in cities:
        s.add(pos[city] >= 0)
        s.add(pos[city] < 7)
    s.add(Distinct([pos[city] for city in cities]))
    
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            key = tuple(sorted([c1, c2]))
            if key not in edge_set:
                diff = pos[c1] - pos[c2]
                s.add(Or(diff >= 2, diff <= -2))
    
    starts = {}
    ends = {}
    for city in cities:
        sum_before = Sum([If(pos[other] < pos[city], durations[other], 0) for other in cities])
        count_before = Sum([If(pos[other] < pos[city], 1, 0) for other in cities])
        start_city = 1 + sum_before - count_before
        end_city = start_city + durations[city] - 1
        starts[city] = start_city
        ends[city] = end_city
    
    stuttgart = cities[0]
    split = cities[3]
    krakow = cities[4]
    s.add(starts['Stuttgart'] <= 13)
    s.add(ends['Stuttgart'] >= 11)
    s.add(starts['Split'] <= 14)
    s.add(ends['Split'] >= 13)
    s.add(starts['Krakow'] <= 11)
    s.add(ends['Krakow'] >= 8)
    
    if s.check() == sat:
        model = s.model()
        order = sorted(cities, key=lambda c: model.eval(pos[c]).as_long())
        itinerary_list = []
        city_stays = []
        for idx, city in enumerate(order):
            start_val = 1
            if idx > 0:
                sum_prev = sum(durations[c] for c in order[:idx])
                start_val = 1 + sum_prev - idx
            end_val = start_val + durations[city] - 1
            city_stays.append((city, start_val, end_val))
        
        for idx, (city, start, end) in enumerate(city_stays):
            itinerary_list.append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })
            if idx < len(city_stays) - 1:
                itinerary_list.append({
                    "day_range": f"Day {end}",
                    "place": city
                })
                next_city = city_stays[idx+1][0]
                itinerary_list.append({
                    "day_range": f"Day {end}",
                    "place": next_city
                })
        
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()