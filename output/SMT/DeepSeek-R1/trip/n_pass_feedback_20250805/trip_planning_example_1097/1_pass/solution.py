from z3 import *

def main():
    # Define cities and their indices
    cities = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    n_days = 18
    n_cities = len(cities)
    
    # Required days per city: [Reykjavik, Riga, Oslo, Lyon, Dubrovnik, Madrid, Warsaw, London]
    required_days = [4, 2, 3, 5, 2, 2, 4, 3]
    
    # Define direct flights as undirected edges (min, max)
    edges = [
        (0, 6), (2, 5), (6, 1), (3, 7), (5, 7), (6, 7), (0, 5), (6, 2), (2, 4),
        (0, 2), (1, 2), (2, 3), (2, 7), (0, 7), (6, 5), (5, 3), (4, 5)
    ]
    flights_set = set()
    for a, b in edges:
        if a > b:
            flights_set.add((b, a))
        else:
            flights_set.add((a, b))
    
    # Create solver and variables for the end city of each day
    s = Solver()
    day_end = [Int(f'day_{i+1}') for i in range(n_days)]
    
    # Each day_end must be between 0 and 7
    for i in range(n_days):
        s.add(And(day_end[i] >= 0, day_end[i] < n_cities))
    
    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        a = day_end[i]
        b = day_end[i + 1]
        # If cities are different, ensure there's a direct flight
        flight_cond = Or([Or(And(a == c1, b == c2), And(a == c2, b == c1)]) for (c1, c2) in flights_set)
        s.add(If(a != b, flight_cond, True))
    
    # Total days per city constraint
    for c in range(n_cities):
        end_days = [If(day_end[i] == c, 1, 0) for i in range(n_days)]
        departure_days = [If(And(day_end[i - 1] == c, day_end[i] != c), 1, 0) for i in range(1, n_days)]
        total = Sum(end_days) + Sum(departure_days)
        s.add(total == required_days[c])
    
    # Specific day constraints
    # Be in Riga (index 1) on day 4 or 5
    day4_end = (day_end[3] == 1)
    day4_departure = And(day_end[2] == 1, day_end[3] != 1)
    day5_end = (day_end[4] == 1)
    day5_departure = And(day_end[3] == 1, day_end[4] != 1)
    s.add(Or(day4_end, day4_departure, day5_end, day5_departure))
    
    # Be in Dubrovnik (index 4) on day 7 or 8
    day7_end = (day_end[6] == 4)
    day7_departure = And(day_end[5] == 4, day_end[6] != 4)
    day8_end = (day_end[7] == 4)
    day8_departure = And(day_end[6] == 4, day_end[7] != 4)
    s.add(Or(day7_end, day7_departure, day8_end, day8_departure))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_index = m.evaluate(day_end[i]).as_long()
            itinerary.append(cities[city_index])
        
        # Output as JSON-formatted dictionary
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()