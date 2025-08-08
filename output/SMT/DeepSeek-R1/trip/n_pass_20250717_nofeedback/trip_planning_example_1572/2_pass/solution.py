from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Seville', 'Paris', 'Lyon', 'Nice', 'Naples', 'Zurich', 'Stockholm', 'Riga']
    
    # Create Z3 variables for start and end days of each city
    start_vars = {city: Int(f'start_{city}') for city in cities}
    end_vars = {city: Int(f'end_{city}') for city in cities}
    
    s = Solver()
    
    # Each city must have a duration of at least 2 days
    for city in cities:
        s.add(start_vars[city] >= 1)
        s.add(end_vars[city] <= 23)
        s.add(end_vars[city] - start_vars[city] + 1 >= 2)
    
    # Ensure no overlaps: for any two distinct cities, one must end before the other starts
    for i in range(len(cities)):
        for j in range(i + 1, len(cities)):
            city1 = cities[i]
            city2 = cities[j]
            s.add(Or(
                end_vars[city1] < start_vars[city2],
                end_vars[city2] < start_vars[city1]
            ))
    
    # At least one city must start on day 1 and at least one city must end on day 23
    s.add(Or([start_vars[city] == 1 for city in cities]))
    s.add(Or([end_vars[city] == 23 for city in cities]))
    
    # Total days must sum to 23
    total_days = Int('total_days')
    s.add(total_days == Sum([end_vars[city] - start_vars[city] + 1 for city in cities]))
    s.add(total_days == 23)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for city in cities:
            s_val = model.eval(start_vars[city]).as_long()
            e_val = model.eval(end_vars[city]).as_long()
            itinerary.append((s_val, e_val, city))
        
        # Sort by start day
        itinerary.sort(key=lambda x: x[0])
        
        # Format the itinerary
        result = []
        for s_val, e_val, city in itinerary:
            day_range = f"Day {s_val}-{e_val}"
            result.append({'day_range': day_range, 'place': city})
        
        plan = {'itinerary': result}
        print(plan)
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()