from z3 import *

def main():
    cities = ['P', 'B', 'T', 'S']  # P: Prague, B: Berlin, T: Tallinn, S: Stockholm
    n_days = 12
    days = list(range(1, n_days+1))
    
    # Create Z3 variables: in_city[d][c] is True if in city c on day d
    in_city = {}
    for d in days:
        for c in cities:
            in_city[(d, c)] = Bool(f"day{d}_city{c}")
    
    s = Solver()
    
    # Constraint 1: Each day must be in at least one city, at most two cities
    for d in days:
        s.add(Or([in_city[(d, c)] for c in cities]))
        s.add(AtMost(in_city[(d, 'P')], in_city[(d, 'B')], in_city[(d, 'T')], in_city[(d, 'S')], 2))
        # Disallow Prague and Berlin together (no direct flight)
        s.add(Not(And(in_city[(d, 'P')], in_city[(d, 'B')])))
    
    # Constraint 2: Consecutive days must share at least one city
    for i in range(1, n_days):
        s.add(Or([And(in_city[(i, c)], in_city[(i+1, c)]) for c in cities]))
    
    # Constraint 3: Total days per city
    s.add(Sum([If(in_city[(d, 'P')], 1, 0) for d in days]) == 2)  # Prague
    s.add(Sum([If(in_city[(d, 'B')], 1, 0) for d in days]) == 3)  # Berlin
    s.add(Sum([If(in_city[(d, 'T')], 1, 0) for d in days]) == 5)  # Tallinn
    s.add(Sum([If(in_city[(d, 'S')], 1, 0) for d in days]) == 5)  # Stockholm
    
    # Constraint 4: Specific day requirements
    s.add(in_city[(6, 'B')] == True)  # Must be in Berlin on day 6
    s.add(in_city[(8, 'B')] == True)  # Must be in Berlin on day 8
    # Must be in Tallinn every day from 8 to 12
    for d in range(8, 13):
        s.add(in_city[(d, 'T')] == True)
    
    # Solve and output itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in days:
            places = []
            for c in cities:
                if is_true(model[in_city[(d, c)]]):
                    places.append(c)
            itinerary.append({"day": d, "place": sorted(places)})
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()