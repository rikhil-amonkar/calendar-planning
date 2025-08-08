from z3 import *

def main():
    s = Solver()
    
    cities = ['Santorini', 'Vienna', 'Madrid', 'Seville', 'Valencia', 'Krakow', 'Frankfurt', 'Bucharest', 'Riga', 'Tallinn']
    n = len(cities)
    
    # Start days for each trip
    starts = [Int(f'start_{i}') for i in range(n)]
    # Durations for each trip
    durations = [Int(f'duration_{i}') for i in range(n)]
    # City assignment for each trip (index into cities list)
    city_assignments = [Int(f'city_{i}') for i in range(n)]
    
    # Constraint: First trip starts on day 1
    s.add(starts[0] == 1)
    
    # Constraints for subsequent start days: start[i] = start[i-1] + duration[i-1]
    for i in range(1, n):
        s.add(starts[i] == starts[i-1] + durations[i-1])
    
    # Constraint: Last trip must end on day 27
    s.add(starts[n-1] + durations[n-1] - 1 == 27)
    
    # Constraints for durations: each between 2 and 5 inclusive
    for i in range(n):
        s.add(durations[i] >= 2, durations[i] <= 5)
    
    # Constraints for city assignments: each must be between 0 and n-1
    for i in range(n):
        s.add(city_assignments[i] >= 0, city_assignments[i] < n)
    
    # Constraint: All city assignments must be distinct (permutation)
    s.add(Distinct(city_assignments))
    
    if s.check() == sat:
        model = s.model()
        start_days = [model.evaluate(starts[i]).as_long() for i in range(n)]
        duration_days = [model.evaluate(durations[i]).as_long() for i in range(n)]
        city_indices = [model.evaluate(city_assignments[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            start = start_days[i]
            duration = duration_days[i]
            end = start + duration - 1
            city = cities[city_indices[i]]
            itinerary.append({
                'day_range': f'Day {start}-{end}',
                'place': city
            })
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()