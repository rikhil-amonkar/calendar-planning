from z3 import *

def main():
    cities = ['P', 'B', 'T', 'S']  # P: Prague, B: Berlin, T: Tallinn, S: Stockholm
    n_days = 12
    days = list(range(n_days))
    
    in_city = {}
    for d in days:
        for c in cities:
            in_city[(d, c)] = Bool(f"day{d}_city{c}")
    
    s = Solver()
    
    # Each day, we are in at least one city and at most two cities.
    for d in days:
        s.add(Or([in_city[(d, c)] for c in cities]))
        s.add(AtMost(in_city[(d, 'P')], in_city[(d, 'B')], in_city[(d, 'T')], in_city[(d, 'S')], 2))
        # Disallow Prague and Berlin on the same day (no direct flight)
        s.add(Not(And(in_city[(d, 'P')], in_city[(d, 'B')])))
    
    # Consecutive days must share at least one city.
    for d in range(n_days - 1):
        common_city = Or([And(in_city[(d, c)], in_city[(d+1, c)]) for c in cities])
        s.add(common_city)
    
    # Total days per city
    s.add(Sum([If(in_city[(d, 'P')], 1, 0) for d in days]) == 2)  # Prague: 2 days
    s.add(Sum([If(in_city[(d, 'B')], 1, 0) for d in days]) == 3)  # Berlin: 3 days
    s.add(Sum([If(in_city[(d, 'T')], 1, 0) for d in days]) == 5)  # Tallinn: 5 days
    s.add(Sum([If(in_city[(d, 'S')], 1, 0) for d in days]) == 5)  # Stockholm: 5 days
    
    # Specific day constraints
    s.add(in_city[(5, 'B')] == True)  # Day 6 must be in Berlin (index 5)
    s.add(in_city[(7, 'B')] == True)  # Day 8 must be in Berlin (index 7)
    # Must be in Tallinn from day 8 to day 12 (indices 7 to 11 inclusive)
    for d in range(7, 12):
        s.add(in_city[(d, 'T')] == True)
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(n_days):
            places = []
            for c in cities:
                if model.evaluate(in_city[(d, c)]):
                    places.append(c)
            itinerary.append({"day": d+1, "place": sorted(places)})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()