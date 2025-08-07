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
    # On days 1 and 2: only Porto
    for day in [1, 2]:
        s.add(In['Porto'][day])
        for other in cities:
            if other != 'Porto':
                s.add(Not(In[other][day]))
    # On day 3: Porto and exactly one other city (flight out)
    s.add(In['Porto'][3])
    s.add(Or(
        And(In['Paris'][3], Not(In['Florence'][3]), Not(In['Vienna'][3]), Not(In['Munich'][3]), Not(In['Nice'][3]), Not(In['Warsaw'][3])),
        And(In['Florence'][3], Not(In['Paris'][3]), Not(In['Vienna'][3]), Not(In['Munich'][3]), Not(In['Nice'][3]), Not(In['Warsaw'][3])),
        And(In['Vienna'][3], Not(In['Paris'][3]), Not(In['Florence'][3]), Not(In['Munich'][3]), Not(In['Nice'][3]), Not(In['Warsaw'][3])),
        And(In['Munich'][3], Not(In['Paris'][3]), Not(In['Florence'][3]), Not(In['Vienna'][3]), Not(In['Nice'][3]), Not(In['Warsaw'][3])),
        And(In['Nice'][3], Not(In['Paris'][3]), Not(In['Florence'][3]), Not(In['Vienna'][3]), Not(In['Munich'][3]), Not(In['Warsaw'][3])),
        And(In['Warsaw'][3], Not(In['Paris'][3]), Not(In['Florence'][3]), Not(In['Vienna'][3]), Not(In['Munich'][3]), Not(In['Nice'][3]))
    ))

    # Fixed constraints for Warsaw: days 13,14,15
    # On days 13 and 14: only Warsaw
    for day in [13, 14]:
        s.add(In['Warsaw'][day])
        for other in cities:
            if other != 'Warsaw':
                s.add(Not(In[other][day]))
    # On day 15: Warsaw and exactly one other city (flight out)
    s.add(In['Warsaw'][15])
    s.add(Or(
        And(In['Paris'][15], Not(In['Florence'][15]), Not(In['Vienna'][15]), Not(In['Porto'][15]), Not(In['Munich'][15]), Not(In['Nice'][15])),
        And(In['Florence'][15], Not(In['Paris'][15]), Not(In['Vienna'][15]), Not(In['Porto'][15]), Not(In['Munich'][15]), Not(In['Nice'][15])),
        And(In['Vienna'][15], Not(In['Paris'][15]), Not(In['Florence'][15]), Not(In['Porto'][15]), Not(In['Munich'][15]), Not(In['Nice'][15])),
        And(In['Porto'][15], Not(In['Paris'][15]), Not(In['Florence'][15]), Not(In['Vienna'][15]), Not(In['Munich'][15]), Not(In['Nice'][15])),
        And(In['Munich'][15], Not(In['Paris'][15]), Not(In['Florence'][15]), Not(In['Vienna'][15]), Not(In['Porto'][15]), Not(In['Nice'][15])),
        And(In['Nice'][15], Not(In['Paris'][15]), Not(In['Florence'][15]), Not(In['Vienna'][15]), Not(In['Porto'][15]), Not(In['Munich'][15]))
    ))

    # Fixed constraints for Vienna: days 19,20: only Vienna
    for day in [19, 20]:
        s.add(In['Vienna'][day])
        for other in cities:
            if other != 'Vienna':
                s.add(Not(In[other][day]))

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
        # Count the number of cities on day d and d+1
        count_d = Sum([If(In[city][d], 1, 0) for city in cities])
        count_next = Sum([If(In[city][d+1], 1, 0) for city in cities])
        
        # Case 1: we are in exactly one city on day d and the same city on day d+1
        same_city = True
        for city in cities:
            same_city = And(same_city, (In[city][d] == In[city][d+1]))
        case1 = And(count_d == 1, count_next == 1, same_city)
        
        # Case 2: we are in two cities on day d and one city on day d+1
        flight_conds = []
        for city1 in cities:
            for city2 in cities:
                if city1 == city2:
                    continue
                # Condition for leaving city1 and staying in city2, if there is flight from city1 to city2
                if (city1, city2) in flight_edges:
                    cond1 = And(
                        In[city1][d],
                        Not(In[city1][d+1]),
                        In[city2][d],
                        In[city2][d+1]
                    )
                    flight_conds.append(cond1)
                # Condition for leaving city2 and staying in city1, if there is flight from city2 to city1
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