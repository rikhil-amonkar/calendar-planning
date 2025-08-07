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
    ends = [Int(f'end_{i}') for i in range(n)]  # New end day variables
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
    
    # Relationship between start, end, and duration
    for i in range(n):
        solver.add(ends[i] == starts[i] + durations[i] - 1)
        solver.add(durations[i] > 0)
        solver.add(starts[i] > 0)
        solver.add(ends[i] > 0)
    
    # Trip structure constraints
    solver.add(starts[0] == 1)  # Trip starts on day 1
    solver.add(ends[-1] == 18)  # Trip ends on day 18
    
    # Contiguous stays: each next stay starts immediately after previous ends
    for i in range(n - 1):
        solver.add(starts[i+1] == ends[i] + 1)
    
    # Total duration constraint
    total_duration = Sum(durations)
    solver.add(total_duration == 18)
    
    # Allow exactly one city to be below minimum duration
    meet_min = [Bool(f'meet_min_{i}') for i in range(n)]
    for i in range(n):
        solver.add(meet_min[i] == (durations[i] >= min_dur_array[city_vars[i]]))
    solver.add(Sum([If(meet_min[i], 1, 0) for i in range(n)]) == n-1)
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            s = model.evaluate(starts[i]).as_long()
            e = model.evaluate(ends[i]).as_long()
            city_idx = model.evaluate(city_vars[i]).as_long()
            city_name = city_names[city_idx]
            day_range = f"Day {s}-{e}" if e > s else f"Day {s}"
            itinerary.append({'day_range': day_range, 'place': city_name})
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()