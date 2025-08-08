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
    min_durs = [3, 2, 3, 3, 3, 2, 3]  # Min durations matching city_names order
    
    # Create solver and variables
    solver = Solver()
    starts = [Int(f'start_{i}') for i in range(n)]
    durations = [Int(f'duration_{i}') for i in range(n)]
    city_vars = [Int(f'city_{i}') for i in range(n)]
    
    # City assignment constraints
    for i in range(n):
        solver.add(city_vars[i] >= 0, city_vars[i] < n)
    solver.add(Distinct(city_vars))
    
    # Duration array for city minimums
    min_dur_array = Array('min_dur_array', IntSort(), IntSort())
    for idx in range(n):
        solver.add(min_dur_array[idx] == min_durs[idx])
    
    # Duration constraints using array lookup
    for i in range(n):
        solver.add(durations[i] >= min_dur_array[city_vars[i]])
    
    # Trip structure constraints
    solver.add(starts[0] == 1)  # Starts on day 1
    for i in range(n - 1):
        # Next stay starts immediately after current ends
        solver.add(starts[i+1] == starts[i] + durations[i])
    # Entire trip ends on day 18
    solver.add(starts[-1] + durations[-1] - 1 == 18)
    
    # Positive durations
    for i in range(n):
        solver.add(durations[i] > 0)
        solver.add(starts[i] > 0)
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            s = model.evaluate(starts[i]).as_long()
            d = model.evaluate(durations[i]).as_long()
            end = s + d - 1
            city_idx = model.evaluate(city_vars[i]).as_long()
            city_name = city_names[city_idx]
            day_range = f"Day {s}-{end}" if d > 1 else f"Day {s}"
            itinerary.append({'day_range': day_range, 'place': city_name})
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()