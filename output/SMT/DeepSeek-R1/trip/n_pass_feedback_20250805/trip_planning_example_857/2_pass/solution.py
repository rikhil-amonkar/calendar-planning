from z3 import *

def main():
    n = 7  # number of stays
    min_durations = {
        'Hamburg': 3,
        'Frankfurt': 2,
        'Naples': 3,
        'Mykonos': 3,
        'Geneva': 3,
        'Porto': 2,
        'Manchester': 3
    }
    city_names = ['Hamburg', 'Frankfurt', 'Naples', 'Mykonos', 'Geneva', 'Porto', 'Manchester']
    
    # Create solver and variables
    solver = Solver()
    starts = [Int(f'start_{i}') for i in range(n)]
    durations = [Int(f'duration_{i}') for i in range(n)]
    city_vars = [Int(f'city_{i}') for i in range(n)]
    
    # Each city is represented by an integer (0 to 6), and all must be distinct
    for i in range(n):
        solver.add(city_vars[i] >= 0, city_vars[i] < n)
    solver.add(Distinct(city_vars))
    
    # First stay starts on day 1
    solver.add(starts[0] == 1)
    
    # Consecutive stays: next start = current start + current duration
    for i in range(n - 1):
        solver.add(starts[i+1] == starts[i] + durations[i])
    
    # Total trip ends on day 18
    solver.add(starts[n-1] + durations[n-1] - 1 == 18)
    
    # Duration constraints based on assigned city
    for i in range(n):
        c = city_vars[i]
        solver.add(Or(
            And(c == 0, durations[i] >= min_durations['Hamburg']),
            And(c == 1, durations[i] >= min_durations['Frankfurt']),
            And(c == 2, durations[i] >= min_durations['Naples']),
            And(c == 3, durations[i] >= min_durations['Mykonos']),
            And(c == 4, durations[i] >= min_durations['Geneva']),
            And(c == 5, durations[i] >= min_durations['Porto']),
            And(c == 6, durations[i] >= min_durations['Manchester'])
        ))
    
    # Ensure positive durations
    for i in range(n):
        solver.add(durations[i] > 0)
        solver.add(starts[i] > 0)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            s = model.evaluate(starts[i]).as_long()
            d = model.evaluate(durations[i]).as_long()
            end = s + d - 1
            city_idx = model.evaluate(city_vars[i]).as_long()
            city_name = city_names[city_idx]
            day_range = f"Day {s}-{end}" if s != end else f"Day {s}"
            itinerary.append({'day_range': day_range, 'place': city_name})
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()