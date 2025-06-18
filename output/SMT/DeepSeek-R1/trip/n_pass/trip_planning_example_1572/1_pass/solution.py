from z3 import *
import json

def main():
    cities = ['Berlin', 'Nice', 'Stockholm', 'Lyon', 'Paris', 'Riga', 'Zurich', 'Seville', 'Milan', 'Naples']
    dur = {
        'Berlin': 2,
        'Nice': 2,
        'Stockholm': 3,
        'Lyon': 3,
        'Paris': 5,
        'Riga': 2,
        'Zurich': 5,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }
    dur_minus_one = {city: dur[city] - 1 for city in cities}

    flight_list = [
        "Paris and Stockholm", "Seville and Paris", "Naples and Zurich", "Nice and Riga", 
        "Berlin and Milan", "Paris and Zurich", "Paris and Nice", "Milan and Paris", 
        "Milan and Riga", "Paris and Lyon", "Milan and Naples", "Paris and Riga", 
        "Berlin and Stockholm", "Stockholm and Riga", "Nice and Zurich", "Milan and Zurich", 
        "Lyon and Nice", "Zurich and Stockholm", "Zurich and Riga", "Berlin and Naples", 
        "Milan and Stockholm", "Berlin and Zurich", "Milan and Seville", "Paris and Naples", 
        "Berlin and Riga", "Nice and Stockholm", "Berlin and Paris", "Nice and Naples", 
        "Berlin and Nice"
    ]

    allowed_pairs_set = set()
    for s in flight_list:
        a, b = s.split(' and ')
        allowed_pairs_set.add((a, b))
        allowed_pairs_set.add((b, a))

    s = Solver()

    pos = {}
    for city in cities:
        pos[city] = Int(f'pos_{city}')
        s.add(pos[city] >= 0, pos[city] < 10)

    s.add(Distinct([pos[city] for city in cities]))
    s.add(pos['Berlin'] == 0)

    cumulative_nice = Sum([If(pos[other] < pos['Nice'], dur_minus_one[other], 0) for other in cities if other != 'Nice'])
    s.add(cumulative_nice == 11)

    cumulative_stockholm = Sum([If(pos[other] < pos['Stockholm'], dur_minus_one[other], 0) for other in cities if other != 'Stockholm'])
    s.add(cumulative_stockholm == 19)

    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            if (c1, c2) not in allowed_pairs_set:
                s.add(Abs(pos[c1] - pos[c2]) != 1)

    if s.check() == sat:
        m = s.model()
        position_values = {}
        for city in cities:
            position_values[city] = m.evaluate(pos[city]).as_long()
        
        ordered_cities = sorted(cities, key=lambda c: position_values[c])
        
        start_days = []
        current = 1
        for city in ordered_cities:
            start_days.append((city, current))
            current = current + dur[city] - 1
        
        itinerary = []
        for idx, (city, start) in enumerate(start_days):
            end = start + dur[city] - 1
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            if idx < len(ordered_cities) - 1:
                itinerary.append({"day_range": f"Day {end}", "place": city})
                next_city = ordered_cities[idx+1]
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()