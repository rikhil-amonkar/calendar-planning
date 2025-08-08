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

    In = {}
    for d in range(1, 21):
        In[d] = {}
        for c in cities:
            In[d][c] = Bool(f"day{d}_{c}")

    s = Solver()

    for d in range(1, 21):
        s.add(Or([In[d][c] for c in cities]))
        s.add(Sum([If(In[d][c], 1, 0) for c in cities]) <= 2)

    for c in cities:
        total = Sum([If(In[d][c], 1, 0) for d in range(1, 21)])
        s.add(total == required_days[c])

    for d in range(1, 21):
        for (c1, c2) in non_edges:
            s.add(Or(Not(In[d][c1]), Not(In[d][c2])))

    s.add(Or(In[11]['Stuttgart'], In[12]['Stuttgart'], In[13]['Stuttgart']))
    s.add(Or(In[13]['Split'], In[14]['Split']))
    s.add(Or(In[8]['Krakow'], In[9]['Krakow'], In[10]['Krakow'], In[11]['Krakow']))

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in range(1, 21):
            cities_today = []
            for c in cities:
                if is_true(m[In[d][c]]):
                    cities_today.append(c)
            cities_today.sort()
            itinerary_list.append({"day": d, "city": cities_today})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()