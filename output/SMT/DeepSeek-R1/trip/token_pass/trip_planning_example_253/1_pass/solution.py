from z3 import *
import json

def main():
    # Initialize solver
    s = Solver()
    
    # Cities and their indices
    cities = ['Vienna', 'Santorini', 'Amsterdam', 'Lyon']
    n_days = 14
    n_cities = len(cities)
    
    # Direct flights (as index pairs, normalized with min first)
    allowed_pairs = set([(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)])
    
    # Create assignment variables: assignments[day][city]
    assignments = [[Bool(f"day_{i+1}_city_{c}") for c in range(n_cities)] for i in range(n_days)]
    
    # Constraint: Each day must have at least one city
    for i in range(n_days):
        s.add(Or(assignments[i]))
    
    # Constraint: No day can have more than two cities
    for i in range(n_days):
        count = Sum([If(assignments[i][c], 1, 0) for c in range(n_cities)])
        s.add(count <= 2)
    
    # Define flight days (exactly two cities)
    flight_days = [Sum([If(assignments[i][c], 1, 0) for c in range(n_cities)]) == 2 for i in range(n_days)]
    
    # Constraint: Exactly 3 flight days
    s.add(Sum([If(flight_days[i], 1, 0) for i in range(n_days)]) == 3)
    
    # Total days per city constraints
    vienna_days = Sum([If(assignments[i][0], 1, 0) for i in range(n_days)])
    santorini_days = Sum([If(assignments[i][1], 1, 0) for i in range(n_days)])
    amsterdam_days = Sum([If(assignments[i][2], 1, 0) for i in range(n_days)])
    lyon_days = Sum([If(assignments[i][3], 1, 0) for i in range(n_days)])
    
    s.add(vienna_days == 7)
    s.add(santorini_days == 4)
    s.add(amsterdam_days == 3)
    s.add(lyon_days == 3)
    
    # Fixed day constraints
    # Lyon on days 7 and 8 (indices 6 and 7)
    s.add(assignments[6][3])  # Day 7
    s.add(assignments[7][3])  # Day 8
    # Amsterdam on days 10 and 11 (indices 9 and 10)
    s.add(assignments[9][2])  # Day 10
    s.add(assignments[10][2]) # Day 11
    # Day 9 (index 8): Lyon and Amsterdam
    s.add(assignments[8][3])  # Lyon
    s.add(assignments[8][2])  # Amsterdam
    
    # Direct flight constraints for pairs not in allowed_pairs
    for i in range(n_days):
        for c1 in range(n_cities):
            for c2 in range(c1 + 1, n_cities):
                if (c1, c2) not in allowed_pairs:
                    s.add(Not(And(assignments[i][c1], assignments[i][c2])))
    
    # Continuity constraints between consecutive days
    for i in range(n_days - 1):
        common_city = Or([And(assignments[i][c], assignments[i+1][c]) for c in range(n_cities)])
        s.add(common_city)
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        # Determine days each city is visited
 city_visits = [[] for _ in range(n_cities)]
        for i in range(n_days):
            for c in range(n_cities):
                if is_true(m.evaluate(assignments[i][c])):
                    city_visits[c].append(i+1)
        
        # Generate intervals for each city
        intervals = []
        for c in range(n_cities):
            days = city_visits[c]
            if not days:
                continue
            days.sort()
            start = days[0]
            end = days[0]
            for day in days[1:]:
                if day == end + 1:
                    end = day
                else:
                    intervals.append((start, end, cities[c]))
                    start = day
                    end = day
            intervals.append((start, end, cities[c]))
        
        intervals.sort(key=lambda x: x[0])
        
        # Format itinerary
        itinerary = []
        for start, end, city in intervals:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()