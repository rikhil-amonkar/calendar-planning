from z3 import *

def main():
    cities = ['P', 'B', 'T', 'S']  # P: Prague, B: Berlin, T: Tallinn, S: Stockholm
    n_days = 12
    days = list(range(1, n_days+1))
    
    # Define valid flight connections (unordered pairs)
    valid_pairs = [('B','T'), ('P','T'), ('S','T'), ('P','S'), ('S','B')]
    
    in_city = {}
    for d in days:
        for c in cities:
            in_city[(d, c)] = Bool(f"day{d}_city{c}")
    
    s = Solver()
    
    # Constraint 1: Each day must be in at least one city, at most two cities
    for d in days:
        s.add(Or([in_city[(d, c)] for c in cities]))
        s.add(AtMost(in_city[(d, 'P')], in_city[(d, 'B')], in_city[(d, 'T')], in_city[(d, 'S')], 2))
        
        # Constraint: If two cities on same day, must be valid flight pair
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1, c2 = cities[i], cities[j]
                # Only allow if it's a valid flight pair
                if (c1, c2) not in valid_pairs and (c2, c1) not in valid_pairs:
                    s.add(Not(And(in_city[(d, c1)], in_city[(d, c2)])))
    
    # Constraint 2: Consecutive days must share at least one city
    for i in range(1, n_days):
        s.add(Or([And(in_city[(i, c)], in_city[(i+1, c)]) for c in cities]))
    
    # Constraint 3: Total days per city
    s.add(Sum([If(in_city[(d, 'P')], 1, 0) for d in days]) == 2)  # Prague
    s.add(Sum([If(in_city[(d, 'B')], 1, 0) for d in days]) == 3)  # Berlin
    s.add(Sum([If(in_city[(d, 'T')], 1, 0) for d in days]) == 5)  # Tallinn
    s.add(Sum([If(in_city[(d, 'S')], 1, 0) for d in days]) == 5)  # Stockholm
    
    # Constraint 4: Specific day requirements
    s.add(in_city[(6, 'B')])  # Must be in Berlin on day 6
    s.add(in_city[(8, 'B')])  # Must be in Berlin on day 8
    for d in range(8, 13):    # Must be in Tallinn every day from 8 to 12
        s.add(in_city[(d, 'T')])
    
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