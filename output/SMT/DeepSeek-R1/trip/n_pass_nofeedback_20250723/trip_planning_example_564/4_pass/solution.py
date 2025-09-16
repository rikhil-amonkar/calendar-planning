from z3 import *

def main():
    days = list(range(1, 17))
    cities = ['I', 'R', 'S', 'N', 'T']  # Codes for cities
    
    # Define direct flight connections (undirected)
    edges = [('R','T'), ('S','R'), ('I','N'), ('N','T'), ('R','N'), ('R','I')]
    allowed_pairs = set(tuple(sorted(pair)) for pair in edges)
    
    solver = Solver()
    in_city = {}
    for city in cities:
        for day in days:
            in_city[(city, day)] = Bool(f"in_{city}_{day}")
    
    # Constraint 1: At least one city per day
    for day in days:
        solver.add(Or([in_city[(city, day)] for city in cities]))
    
    # Constraint 2: At most two cities per day
    for day in days:
        solver.add(AtMost(*[in_city[(city, day)] for city in cities], 2))
    
    # Constraint 3: If two cities same day, must be connected
    for day in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1, c2 = cities[i], cities[j]
                if tuple(sorted((c1, c2))) not in allowed_pairs:
                    solver.add(Not(And(in_city[(c1, day)], in_city[(c2, day)])))
    
    # Constraint 4: Fixed days for Istanbul (6-7) and Santorini (13-16)
    for day in days:
        solver.add(in_city[('I', day)] == (day == 6 or day == 7))
        solver.add(in_city[('T', day)] == (13 <= day <= 16))
    
    # Constraint 5: Total days per city
    for city, total in [('R', 3), ('S', 4), ('N', 7)]:
        solver.add(Sum([If(in_city[(city, day)], 1, 0) for day in days]) == total)
    
    # Constraint 6: Valid transitions between consecutive days
    for day in range(1, 16):
        # Option 1: Common city in both days
        common_city = Or([And(in_city[(c, day)], in_city[(c, day+1)]) for c in cities])
        
        # Option 2: Direct flight connection
        flight_connection = False
        for c1 in cities:
            for c2 in cities:
                if c1 != c2 and tuple(sorted((c1, c2))) in allowed_pairs:
                    # Flight on transition day (either day or day+1)
                    on_day = And(in_city[(c1, day)], in_city[(c2, day)])
                    on_next = And(in_city[(c1, day+1)], in_city[(c2, day+1)])
                    # Require presence in both cities on the flight day
                    flight_connection = Or(flight_connection, 
                                          And(in_city[(c1, day)], in_city[(c2, day+1)], on_day),
                                          And(in_city[(c1, day)], in_city[(c2, day+1)], on_next))
        solver.add(Or(common_city, flight_connection))
    
    # Solve and format output
    if solver.check() == sat:
        model = solver.model()
        # Map city codes to names
        city_names = {
            'I': 'Istanbul',
            'R': 'Rome',
            'S': 'Seville',
            'N': 'Naples',
            'T': 'Santorini'
        }
        
        # Collect all city-day assignments
        assignments = []
        for day in days:
            for city in cities:
                if is_true(model[in_city[(city, day)]]):
                    assignments.append((day, city))
        
        # Convert to consecutive day ranges
        city_blocks = {}
        for city in cities:
            days_in_city = [d for d in days if is_true(model[in_city[(city, d)]])]
            blocks = []
            if days_in_city:
                start = end = days_in_city[0]
                for d in days_in_city[1:]:
                    if d == end + 1:
                        end = d
                    else:
                        blocks.append((start, end))
                        start = end = d
                blocks.append((start, end))
            city_blocks[city] = blocks
        
        # Generate itinerary in chronological order
        itinerary = []
        for city, blocks in city_blocks.items():
            for (start, end) in blocks:
                day_range = f"Day {start}" if start == end else f"Day {start}-{end}"
                itinerary.append({
                    'day_range': day_range,
                    'place': city_names[city]
                })
        itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()