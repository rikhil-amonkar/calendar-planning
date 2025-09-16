from z3 import *

def main():
    days = list(range(1, 17))  # Days 1 to 16
    cities = ['I', 'R', 'S', 'N', 'T']  # Istanbul, Rome, Seville, Naples, Santorini
    
    # Define direct flight connections as undirected edges
    edges = [('R','T'), ('S','R'), ('I','N'), ('N','T'), ('R','N'), ('R','I')]
    allowed_pairs = set(tuple(sorted(pair)) for pair in edges)
    
    # Create Z3 solver and variables
    solver = Solver()
    in_city = {}
    for city in cities:
        for day in days:
            in_city[(city, day)] = Bool(f"in_{city}_{day}")
    
    # Constraint 1: Each day has at least one city
    for day in days:
        solver.add(Or([in_city[(city, day)] for city in cities]))
    
    # Constraint 2: Each day has at most two cities
    for day in days:
        solver.add(AtMost(*[in_city[(city, day)] for city in cities], 2))
    
    # Constraint 3: If two cities on same day, must be connected
    for day in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1, c2 = cities[i], cities[j]
                if tuple(sorted((c1, c2))) not in allowed_pairs:
                    solver.add(Not(And(in_city[(c1, day)], in_city[(c2, day)])))
    
    # Constraint 4: Fixed days for Istanbul and Santorini
    # Istanbul only on days 6-7
    for day in days:
        if day == 6 or day == 7:
            solver.add(in_city[('I', day)] == True)
        else:
            solver.add(in_city[('I', day)] == False)
    
    # Santorini only on days 13-16
    for day in days:
        if 13 <= day <= 16:
            solver.add(in_city[('T', day)] == True)
        else:
            solver.add(in_city[('T', day)] == False)
    
    # Constraint 5: Total days per city
    total_days = {}
    for city in ['R', 'S', 'N']:  # I and T are fixed
        total_days[city] = Sum([If(in_city[(city, day)], 1, 0) for day in days])
    solver.add(total_days['R'] == 3)
    solver.add(total_days['S'] == 4)
    solver.add(total_days['N'] == 7)
    
    # Solve the problem
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
        
        # Convert to consecutive day ranges per city
        itinerary = []
        for city in cities:
            city_days = [day for day in days if is_true(model[in_city[(city, day)]])]
            if not city_days:
                continue
            city_days.sort()
            start = city_days[0]
            end = city_days[0]
            for i in range(1, len(city_days)):
                if city_days[i] == end + 1:
                    end = city_days[i]
                else:
                    itinerary.append({
                        'start': start,
                        'end': end,
                        'place': city_names[city]
                    })
                    start = city_days[i]
                    end = city_days[i]
            itinerary.append({
                'start': start,
                'end': end,
                'place': city_names[city]
            })
        
        # Format day ranges and sort by start day
        formatted_itinerary = []
        for entry in itinerary:
            if entry['start'] == entry['end']:
                day_range = f"Day {entry['start']}"
            else:
                day_range = f"Day {entry['start']}-{entry['end']}"
            formatted_itinerary.append({
                'day_range': day_range,
                'place': entry['place']
            })
        formatted_itinerary.sort(key=lambda x: x['day_range'])
        
        print({'itinerary': formatted_itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()