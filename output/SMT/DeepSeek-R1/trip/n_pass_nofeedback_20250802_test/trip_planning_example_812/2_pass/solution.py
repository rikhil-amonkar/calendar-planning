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

    # Fixed constraints for Porto: only days 1,2,3
    for day in days:
        if day in [1, 2, 3]:
            s.add(In['Porto'][day])
        else:
            s.add(Not(In['Porto'][day]))

    # Fixed constraints for Vienna: only days 19,20
    for day in days:
        if day in [19, 20]:
            s.add(In['Vienna'][day])
        else:
            s.add(Not(In['Vienna'][day]))

    # Fixed constraints for Warsaw: only days 13,14,15
    for day in days:
        if day in [13, 14, 15]:
            s.add(In['Warsaw'][day])
        else:
            s.add(Not(In['Warsaw'][day]))

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
        
        # Case 1: we are in exactly one city on day d
        same_set = And([In[city][d] == In[city][d+1] for city in cities])
        case1 = And(count_d == 1, count_next == 1, same_set)
        
        # Case 2: we are in two cities on day d and one city on day d+1
        # Exactly one city is left (i.e., in day d but not day d+1)
        left_cities = [And(In[city][d], Not(In[city][d+1])) for city in cities]
        exactly_one_left = (Sum([If(cond, 1, 0) for cond in left_cities]) == 1)
        
        # For the flight: there must be a pair (A,B) such that:
        #   A is left, B is stayed, and (A->B) is in flight_edges.
        flight_options = []
        for A in cities:
            for B in cities:
                if A != B and (A, B) in flight_edges:
                    cond = And(
                        In[A][d],
                        Not(In[A][d+1]),
                        In[B][d],
                        In[B][d+1]
                    )
                    flight_options.append(cond)
        case2 = And(count_d == 2, count_next == 1, exactly_one_left, Or(flight_options))
        
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