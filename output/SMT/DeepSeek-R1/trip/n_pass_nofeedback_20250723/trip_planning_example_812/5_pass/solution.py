from z3 import *
import json

def main():
    cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    days = list(range(1, 21))  # Days 1 to 20

    # Create a dictionary for the presence variables: In[city][day]
    In = {}
    for city in cities:
        In[city] = {}
        for day in days:
            In[city][day] = Bool(f"In_{city}_{day}")

    s = Solver()

    # Fixed constraints for Porto: days 1,2,3
    for day in [1, 2]:
        s.add(In['Porto'][day])
        for other in cities:
            if other != 'Porto':
                s.add(Not(In[other][day]))
    # Day 3: Porto and exactly one other city (flight out)
    s.add(In['Porto'][3])
    other_cities_porto = [c for c in cities if c != 'Porto']
    s.add(Sum([If(In[c][3], 1, 0) for c in other_cities_porto]) == 1)

    # Fixed constraints for Warsaw: days 13,14,15
    for day in [13, 14]:
        s.add(In['Warsaw'][day])
        for other in cities:
            if other != 'Warsaw':
                s.add(Not(In[other][day]))
    # Day 15: Warsaw and exactly one other city (flight out)
    s.add(In['Warsaw'][15])
    other_cities_warsaw = [c for c in cities if c != 'Warsaw']
    s.add(Sum([If(In[c][15], 1, 0) for c in other_cities_warsaw]) == 1)

    # Fixed constraints for Vienna: days 19,20
    # Day 19: Vienna and exactly one other city (flight in)
    s.add(In['Vienna'][19])
    other_cities_vienna = [c for c in cities if c != 'Vienna']
    s.add(Sum([If(In[c][19], 1, 0) for c in other_cities_vienna]) == 1)
    # Day 20: Only Vienna
    s.add(In['Vienna'][20])
    for c in other_cities_vienna:
        s.add(Not(In[c][20]))

    # Each day, we are in exactly 1 or 2 cities
    for day in days:
        exprs = [If(In[city][day], 1, 0) for city in cities]
        total = Sum(exprs)
        s.add(Or(total == 1, total == 2))

    # Define the flight edges (directed)
    flight_edges = set()
    bidirectional_pairs = [
        ('Florence', 'Vienna'),
        ('Paris', 'Warsaw'),
        ('Munich', 'Vienna'),
        ('Porto', 'Vienna'),
        ('Warsaw', 'Vienna'),
        ('Munich', 'Warsaw'),
        ('Munich', 'Nice'),
        ('Paris', 'Florence'),
        ('Warsaw', 'Nice'),
        ('Porto', 'Munich'),
        ('Porto', 'Nice'),
        ('Paris', 'Vienna'),
        ('Nice', 'Vienna'),
        ('Porto', 'Paris'),
        ('Paris', 'Nice'),
        ('Paris', 'Munich'),
        ('Porto', 'Warsaw')
    ]
    for (a, b) in bidirectional_pairs:
        flight_edges.add((a, b))
        flight_edges.add((b, a))
    flight_edges.add(('Florence', 'Munich'))  # Directed flight

    # Constraints for consecutive days
    for d in range(1, 20):  # d from 1 to 19
        count_d = Sum([If(In[city][d], 1, 0) for city in cities])
        count_next = Sum([If(In[city][d+1], 1, 0) for city in cities])
        
        # Case 1: Stay in the same city with no flight
        same_city = True
        for city in cities:
            same_city = And(same_city, (In[city][d] == In[city][d+1]))
        case1 = And(count_d == 1, count_next == 1, same_city)
        
        # Case 2: Flight from one city to another
        flight_conds = []
        for city1 in cities:
            for city2 in cities:
                if city1 == city2:
                    continue
                if (city1, city2) in flight_edges:
                    cond1 = And(
                        In[city1][d],
                        Not(In[city1][d+1]),
                        In[city2][d],
                        In[city2][d+1]
                    )
                    flight_conds.append(cond1)
                if (city2, city1) in flight_edges:
                    cond2 = And(
                        In[city2][d],
                        Not(In[city2][d+1]),
                        In[city1][d],
                        In[city1][d+1]
                    )
                    flight_conds.append(cond2)
        
        if flight_conds:
            case2 = And(count_d == 2, count_next == 1, Or(flight_conds))
        else:
            case2 = False
            
        s.add(Or(case1, case2))

    # Total days for non-fixed cities
    total_days = {
        'Paris': 5,
        'Florence': 3,
        'Munich': 5,
        'Nice': 5
    }
    for city, total in total_days.items():
        exprs = [If(In[city][day], 1, 0) for day in days]
        s.add(Sum(exprs) == total)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in days:
            for city in cities:
                if is_true(m.evaluate(In[city][day])):
                    itinerary.append({"day": day, "city": city})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()