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

    # Set duration constraints
    for c in cities:
        s.add(start_vars[c] >= 1)
        s.add(end_vars[c] <= 20)
        s.add(end_vars[c] == start_vars[c] + required_days[c] - 1)

    # Create Boolean variables for daily presence
    in_city = {}
    for c in cities:
        for d in range(1, 21):
            in_city[(c, d)] = Bool(f'in_{c}_{d}')

    # Define daily presence based on start and end
    for c in cities:
        for d in range(1, 21):
            s.add(in_city[(c, d)] == And(start_vars[c] <= d, d <= end_vars[c]))

    # Ensure every day is covered by at least one city
    for d in range(1, 21):
        s.add(Or([in_city[(c, d)] for c in cities]))
        s.add(AtMost(*[in_city[(c, d)] for c in cities], 2))

    # Prevent non-connected cities from overlapping
    for c1, c2 in non_edges:
        for d in range(1, 21):
            s.add(Not(And(in_city[(c1, d)], in_city[(c2, d)])))

    # Meeting date constraints
    s.add(Or(And(start_vars['Stuttgart'] <= 13, end_vars['Stuttgart'] >= 11), 
             And(start_vars['Stuttgart'] <= 13, end_vars['Stuttgart'] >= 11)))
    s.add(Or(And(start_vars['Split'] <= 14, end_vars['Split'] >= 13),
             And(start_vars['Split'] <= 14, end_vars['Split'] >= 13)))
    s.add(Or(And(start_vars['Krakow'] <= 11, end_vars['Krakow'] >= 8),
             And(start_vars['Krakow'] <= 11, end_vars['Krakow'] >= 8)))

    # First and last day constraints
    s.add(Sum([If(in_city[(c, 1)], 1, 0) for c in cities]) == 1)
    s.add(Sum([If(in_city[(c, 20)], 1, 0) for c in cities]) == 1)

    # Ensure exactly one city starts on day 1
    s.add(Sum([If(start_vars[c] == 1, 1, 0) for c in cities]) == 1)
    # Ensure exactly one city ends on day 20
    s.add(Sum([If(end_vars[c] == 20, 1, 0) for c in cities]) == 1)

    # Balance starts and ends for inner days
    for d in range(2, 20):
        starts_d = Sum([If(start_vars[c] == d, 1, 0) for c in cities])
        ends_d = Sum([If(end_vars[c] == d, 1, 0) for c in cities])
        s.add(starts_d == ends_d)

    # Ensure connectivity between consecutive days
    for d in range(1, 20):
        s.add(Or([And(in_city[(c, d)], in_city[(c, d+1)]) for c in cities]))

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in range(1, 21):
            cities_today = []
            for c in cities:
                if is_true(m[in_city[(c, d)]]):
                    cities_today.append(c)
            itinerary_list.append({"day": d, "city": sorted(cities_today)})
        print(json.dumps({"itinerary": itinerary_list}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()