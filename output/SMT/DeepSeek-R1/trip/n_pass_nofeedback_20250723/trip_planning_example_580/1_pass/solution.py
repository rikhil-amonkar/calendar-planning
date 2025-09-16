from z3 import *
import json

def main():
    s = Solver()
    days = 23
    cities = ["Geneva", "Paris", "Porto", "Reykjavik", "Oslo"]
    n_cities = len(cities)
    
    # Create a 2D list of Z3 boolean variables: In[d][c] is True if on day d (0-indexed) we are in city c.
    In = [[Bool('In_%d_%s' % (d, c)) for c in cities] for d in range(days)]
    
    # Define valid direct flights (symmetric)
    flight_pairs = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo")
    ]
    flight_set_sym = set()
    for (a, b) in flight_pairs:
        flight_set_sym.add((a, b))
        flight_set_sym.add((b, a))
    
    # Fixed constraints: Geneva from day1 to day7 (days 0 to 6 in 0-indexing)
    geneva_idx = cities.index("Geneva")
    for d in range(0, 7):  # days 1 to 7 (0-indexed: 0 to 6)
        s.add(In[d][geneva_idx] == True)
        # On these days, we are only in Geneva, except day7 (d=6) which will have two cities
        if d < 6:  # days 1-6: only Geneva
            for idx in range(n_cities):
                if idx != geneva_idx:
                    s.add(In[d][idx] == False)
    
    # Day7 (d=6): In Geneva and one other city connected by direct flight
    d6 = 6  # 0-indexed for day7
    s.add(In[d6][geneva_idx] == True)
    other_cities_day7 = [In[d6][i] for i in range(n_cities) if i != geneva_idx]
    s.add(AtLeast(*other_cities_day7, 1))
    s.add(AtMost(*other_cities_day7, 1))
    for i, city in enumerate(cities):
        if i == geneva_idx:
            continue
        if ("Geneva", city) not in flight_set_sym:
            s.add(Not(In[d6][i]))
    
    # Fixed constraints: Oslo from day19 to day23 (0-indexed days 18 to 22)
    oslo_idx = cities.index("Oslo")
    for d in range(18, 23):  # days 19 to 23 (0-indexed: 18 to 22)
        s.add(In[d][oslo_idx] == True)
        if d == 18:  # day19: also one other city connected by direct flight
            other_cities_day19 = [In[d][i] for i in range(n_cities) if i != oslo_idx]
            s.add(AtLeast(*other_cities_day19, 1))
            s.add(AtMost(*other_cities_day19, 1))
            for i, city in enumerate(cities):
                if i == oslo_idx:
                    continue
                if ("Oslo", city) not in flight_set_sym:
                    s.add(Not(In[d][i]))
        else:  # days 20-23: only Oslo
            for idx in range(n_cities):
                if idx != oslo_idx:
                    s.add(In[d][idx] == False)
    
    # Total days per city constraints
    geneva_total = Sum([If(In[d][geneva_idx], 1, 0) for d in range(days)])
    paris_idx = cities.index("Paris")
    paris_total = Sum([If(In[d][paris_idx], 1, 0) for d in range(days)])
    porto_idx = cities.index("Porto")
    porto_total = Sum([If(In[d][porto_idx], 1, 0) for d in range(days)])
    reykjavik_idx = cities.index("Reykjavik")
    reykjavik_total = Sum([If(In[d][reykjavik_idx], 1, 0) for d in range(days)])
    oslo_total = Sum([If(In[d][oslo_idx], 1, 0) for d in range(days)])
    
    s.add(geneva_total == 7)
    s.add(paris_total == 6)
    s.add(porto_total == 7)
    s.add(reykjavik_total == 2)
    s.add(oslo_total == 5)
    
    # Every day: at least one city, at most two cities
    for d in range(days):
        total_cities = Sum([If(In[d][i], 1, 0) for i in range(n_cities)])
        s.add(total_cities >= 1)
        s.add(total_cities <= 2)
    
    # For any day with two cities, they must be connected by a direct flight
    for d in range(days):
        for i in range(n_cities):
            for j in range(i+1, n_cities):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in flight_set_sym:
                    s.add(Not(And(In[d][i], In[d][j])))
    
    # There are exactly 4 days with two cities (flight days: 7, 13, 18, 19)
    two_city_days = [If(Sum([If(In[d][i], 1, 0) for i in range(n_cities)]) == 2, 1, 0) for d in range(days)]
    s.add(Sum(two_city_days) == 4)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in range(days):
            for i in range(n_cities):
                if m.evaluate(In[d][i]):
                    day_num = d + 1
                    itinerary_list.append({"day": day_num, "city": cities[i]})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()