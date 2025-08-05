from z3 import *

def main():
    # Define days and cities
    days = list(range(1, 17))  # Days 1 to 16
    cities = ['I', 'R', 'S', 'N', 'T']  # Istanbul, Rome, Seville, Naples, Santorini
    
    # Define direct flight connections (as undirected edges)
    allowed_pairs = [('R', 'T'), ('S', 'R'), ('I', 'N'), ('N', 'T'), ('R', 'N'), ('R', 'I')]
    # Convert to canonical sorted tuples to avoid duplicates
    allowed_pairs_canon = set()
    for pair in allowed_pairs:
        sorted_pair = tuple(sorted(pair))
        allowed_pairs_canon.add(sorted_pair)
    
    # Create Z3 solver and variables
    solver = Solver()
    in_city = {}
    for city in cities:
        city_days = {}
        for day in days:
            city_days[day] = Bool(f"in_{city}_{day}")
        in_city[city] = city_days
    
    # Constraint 1: Each day, at least one city is true.
    for day in days:
        solver.add(Or([in_city[city][day] for city in cities]))
    
    # Constraint 2: Each day, at most two cities are true.
    for day in days:
        cities_day = [in_city[city][day] for city in cities]
        solver.add(AtMost(*cities_day, 2))
    
    # Constraint 3: For any two distinct cities on the same day, if both are true, they must form an allowed pair.
    for day in days:
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in allowed_pairs_canon and (c2, c1) not in allowed_pairs_canon:
                    # Since we use sorted tuples, one of these orders should be in the set, but we check both for safety.
                    sorted_pair = tuple(sorted([c1, c2]))
                    if sorted_pair not in allowed_pairs_canon:
                        solver.add(Not(And(in_city[c1][day], in_city[c2][day])))
    
    # Constraint 4: Total days per city and fixed days.
    # Istanbul: 2 days, including days 6 and 7.
    for d in [6, 7]:
        solver.add(in_city['I'][d] == True)
    total_I = Sum([If(in_city['I'][d], 1, 0) for d in days])
    solver.add(total_I == 2)
    
    # Rome: 3 days
    total_R = Sum([If(in_city['R'][d], 1, 0) for d in days])
    solver.add(total_R == 3)
    
    # Seville: 4 days
    total_S = Sum([If(in_city['S'][d], 1, 0) for d in days])
    solver.add(total_S == 4)
    
    # Naples: 7 days
    total_N = Sum([If(in_city['N'][d], 1, 0) for d in days])
    solver.add(total_N == 7)
    
    # Santorini: 4 days, including days 13-16.
    for d in [13, 14, 15, 16]:
        solver.add(in_city['T'][d] == True)
    total_T = Sum([If(in_city['T'][d], 1, 0) for d in days])
    solver.add(total_T == 4)
    
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
                if model.evaluate(in_city[city][day]):
                    itinerary.append({"day": day, "place": city_names[city]})
        # Output as JSON dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()