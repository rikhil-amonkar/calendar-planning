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
    for day in range(1, 20):
        L_list = []  # Conditions for leaving a city: In[city][day] and not In[city][day+1]
        R_list = []  # Conditions for arriving: not In[city][day] and In[city][day+1]
        for city in cities:
            condL = And(In[city][day], Not(In[city][day+1]))
            condR = And(Not(In[city][day]), In[city][day+1])
            L_list.append(condL)
            R_list.append(condR)
        
        # At most one city is left, and no city is newly arrived without being present on the flight day
        s.add(AtMost(*L_list, 1))
        s.add(Sum([If(r, 1, 0) for r in R_list]) == 0)
        
        # If a city A is left, there must be a city B (connected by flight) present on both days
        for idx, A in enumerate(cities):
            if L_list[idx] == False:
                continue
            other_cities = [B for B in cities if B != A]
            constraints = []
            for B in other_cities:
                # B must be present on day and day+1, and flight from A to B must exist
                constraints.append(And(In[B][day], In[B][day+1], (A, B) in flight_edges))
            s.add(Implies(L_list[idx], Or(constraints)))
        
        # If no city is left, then the set of cities remains the same
        no_flight = And([Not(l) for l in L_list])
        same_set = And([In[city][day] == In[city][day+1] for city in cities])
        s.add(Implies(no_flight, same_set))

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