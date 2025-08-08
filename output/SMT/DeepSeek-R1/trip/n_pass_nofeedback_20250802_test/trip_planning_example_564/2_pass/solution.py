from z3 import *

def main():
    days = list(range(1, 17))  # Days 1 to 16
    cities = ['I', 'R', 'S', 'N', 'T']  # Istanbul, Rome, Seville, Naples, Santorini
    
    # Define direct flight connections as undirected edges
    edges = [('R','T'), ('S','R'), ('I','N'), ('N','T'), ('R','N'), ('R','I')]
    allowed_undirected = set(tuple(sorted(pair)) for pair in edges)
    
    # Create Z3 solver and variables
    solver = Solver()
    in_city = {}
    for city in cities:
        for day in days:
            in_city[(city, day)] = Bool(f"in_{city}_{day}")
    
    # Constraint 1: Each day, at least one city is visited.
    for day in days:
        solver.add(Or([in_city[(city, day)] for city in cities]))
    
    # Constraint 2: Each day, at most two cities are visited.
    for day in days:
        city_vars = [in_city[(city, day)] for city in cities]
        solver.add(AtMost(*city_vars, 2))
    
    # Constraint 3: For any two distinct cities on the same day, if both are visited, they must be connected by a direct flight.
    for day in days:
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if tuple(sorted([c1, c2])) not in allowed_undirected:
                    solver.add(Not(And(in_city[(c1, day)], in_city[(c2, day)])))
    
    # Constraint 4: Fixed days for Istanbul and Santorini.
    # Istanbul must be visited only on days 6 and 7.
    for day in days:
        if day == 6 or day == 7:
            solver.add(in_city[('I', day)] == True)
        else:
            solver.add(in_city[('I', day)] == False)
    
    # Santorini must be visited only on days 13-16.
    for day in days:
        if 13 <= day <= 16:
            solver.add(in_city[('T', day)] == True)
        else:
            solver.add(in_city[('T', day)] == False)
    
    # Constraint 5: Total days for each city.
    total_days = {}
    for city in ['R', 'S', 'N']:  # I and T are already fixed
        total_days[city] = Sum([If(in_city[(city, day)], 1, 0) for day in days])
    solver.add(total_days['R'] == 3)
    solver.add(total_days['S'] == 4)
    solver.add(total_days['N'] == 7)
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = {
            'I': 'Istanbul',
            'R': 'Rome',
            'S': 'Seville',
            'N': 'Naples',
            'T': 'Santorini'
        }
        for day in days:
            for city in cities:
                if model.evaluate(in_city[(city, day)]):
                    itinerary.append({"day": day, "place": city_names[city]})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()