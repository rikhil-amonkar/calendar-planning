from z3 import *

def main():
    # Define the cities and days
    cities = ['Nice', 'Krakow', 'Dublin', 'Lyon', 'Frankfurt']
    days = list(range(1, 21))
    
    # Create a solver instance
    s = Solver()
    
    # Create variables: in_city[c, d] is True if the traveler is in city c on day d
    in_city = {}
    for c in cities:
        for d in days:
            in_city[(c, d)] = Bool(f'in_{c}_{d}')
    
    # Constraint: Total days for each city
    s.add(Sum([If(in_city[('Nice', d)], 1, 0) for d in days]) == 5)
    s.add(Sum([If(in_city[('Krakow', d)], 1, 0) for d in days]) == 6)
    s.add(Sum([If(in_city[('Dublin', d)], 1, 0) for d in days]) == 7)
    s.add(Sum([If(in_city[('Lyon', d)], 1, 0) for d in days]) == 4)
    s.add(Sum([If(in_city[('Frankfurt', d)], 1, 0) for d in days]) == 2)
    
    # Constraint: Nice only on days 1-5
    for d in range(6, 21):
        s.add(in_city[('Nice', d)] == False)
    
    # Constraint: Frankfurt only on days 19-20
    s.add(in_city[('Frankfurt', 19)] == True)
    s.add(in_city[('Frankfurt', 20)] == True)
    for d in range(1, 19):
        s.add(in_city[('Frankfurt', d)] == False)
    
    # Constraint: Each day has 1 or 2 cities
    for d in days:
        or_expr = Or(
            Sum([If(in_city[(c, d)], 1, 0) for c in cities]) == 1,
            Sum([If(in_city[(c, d)], 1, 0) for c in cities]) == 2
        )
        s.add(or_expr)
    
    # Constraint: Consecutive days share at least one city
    for d in range(1, 20):
        or_expr = Or([And(in_city[(c, d)], in_city[(c, d+1)]) for c in cities])
        s.add(or_expr)
    
    # Define allowed direct flight pairs
    allowed_pairs = [
        ('Nice', 'Dublin'),
        ('Dublin', 'Frankfurt'),
        ('Dublin', 'Krakow'),
        ('Krakow', 'Frankfurt'),
        ('Lyon', 'Frankfurt'),
        ('Nice', 'Frankfurt'),
        ('Lyon', 'Dublin'),
        ('Nice', 'Lyon')
    ]
    
    # Constraint: For days with two cities, they must be connected by a direct flight
    for d in days:
        total_cities = Sum([If(in_city[(c, d)], 1, 0) for c in cities])
        or_list = []
        for (c1, c2) in allowed_pairs:
            or_list.append(And(in_city[(c1, d)], in_city[(c2, d)]))
        s.add(Implies(total_cities == 2, Or(or_list)))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        # Print the itinerary
        for d in days:
            cities_today = [c for c in cities if model.evaluate(in_city[(c, d)])]
            print(f"Day {d}: {', '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()