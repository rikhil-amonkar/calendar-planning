from z3 import *
import json

def main():
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    required_days = {
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
    allowed_pairs = set()
    for u, v in edges:
        key = tuple(sorted([u, v]))
        allowed_pairs.add(key)
    
    total_pairs = set()
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            key = tuple(sorted([c1, c2]))
            total_pairs.add(key)
    non_edges = total_pairs - allowed_pairs

    start_vars = {}
    end_vars = {}
    for c in cities:
        start_vars[c] = Int(f'start_{c}')
        end_vars[c] = Int(f'end_{c}')

    s = Solver()

    for c in cities:
        s.add(start_vars[c] >= 1)
        s.add(end_vars[c] <= 20)
        s.add(end_vars[c] == start_vars[c] + required_days[c] - 1)

    for d in range(1, 21):
        in_city_list = []
        for c in cities:
            in_city = And(start_vars[c] <= d, d <= end_vars[c])
            in_city_list.append(in_city)
        s.add(Or(in_city_list))
        s.add(Sum([If(cond, 1, 0) for cond in in_city_list]) <= 2)

    for (c1, c2) in non_edges:
        s.add(Or(end_vars[c1] < start_vars[c2], end_vars[c2] < start_vars[c1]))

    s.add(And(start_vars['Stuttgart'] <= 13, end_vars['Stuttgart'] >= 11))
    s.add(And(start_vars['Split'] <= 14, end_vars['Split'] >= 13))
    s.add(And(start_vars['Krakow'] <= 11, end_vars['Krakow'] >= 8))

    d1_count = Sum([If(And(start_vars[c] <= 1, 1 <= end_vars[c]), 1, 0) for c in cities])
    s.add(d1_count == 1)

    d20_count = Sum([If(And(start_vars[c] <= 20, 20 <= end_vars[c]), 1, 0) for c in cities])
    s.add(d20_count == 1)

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in range(1, 21):
            cities_today = []
            for c in cities:
                start_val = m[start_vars[c]].as_long()
                end_val = m[end_vars[c]].as_long()
                if start_val <= d <= end_val:
                    cities_today.append(c)
            cities_today.sort()
            itinerary_list.append({"day": d, "city": cities_today})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()