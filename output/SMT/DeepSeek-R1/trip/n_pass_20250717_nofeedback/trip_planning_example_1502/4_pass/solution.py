from z3 import *

def main():
    s = Solver()
    
    cities = ['Santorini', 'Vienna', 'Madrid', 'Seville', 'Valencia', 'Krakow', 'Frankfurt', 'Bucharest', 'Riga', 'Tallinn']
    n = len(cities)
    
    # Start days for each trip
    starts = [Int(f'start_{i}') for i in range(n)]
    # End days for each trip
    ends = [Int(f'end_{i}') for i in range(n)]
    # Durations for each trip
    durations = [Int(f'duration_{i}') for i in range(n)]
    # City assignment for each trip (index into cities list)
    city_assignments = [Int(f'city_{i}') for i in range(n)]
    
    # Duration constraints: each trip lasts 2-5 days
    for i in range(n):
        s.add(durations[i] >= 2, durations[i] <= 5)
    
    # Relationship between start, end, and duration
    for i in range(n):
        s.add(ends[i] == starts[i] + durations[i] - 1)
    
    # First trip starts on day 1
    s.add(starts[0] == 1)
    
    # Adjacency constraints: end of trip i + 1 = start of trip i+1
    for i in range(n-1):
        s.add(ends[i] + 1 == starts[i+1])
    
    # Last trip ends on day 27
    s.add(ends[n-1] == 27)
    
    # City assignment constraints
    for i in range(n):
        s.add(city_assignments[i] >= 0, city_assignments[i] < n)
    s.add(Distinct(city_assignments))
    
    # Verify and output solution
    if s.check() == sat:
        model = s.model()
        start_vals = [model.evaluate(starts[i]).as_long() for i in range(n)]
        end_vals = [model.evaluate(ends[i]).as_long() for i in range(n)]
        city_vals = [model.evaluate(city_assignments[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_idx = city_vals[i]
            itinerary.append({
                'day_range': f'Day {start_vals[i]}-{end_vals[i]}',
                'place': cities[city_idx]
            })
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()