from z3 import Solver, Int, And, Or, sat

def main():
    cities = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
    n = len(cities)
    total_days = 20
    
    # Duration variables for each city (2-4 days)
    durations = [Int(f'd_{i}') for i in range(n)]
    
    solver = Solver()
    
    # Each duration must be between 2 and 4
    for d in durations:
        solver.add(And(d >= 2, d <= 4))
    
    # Total days must sum to 20
    solver.add(sum(durations) == total_days)
    
    # Compute start days based on durations
    starts = [1]  # First city starts on day 1
    for i in range(n-1):
        starts.append(starts[-1] + durations[i])
    
    # Last city must end by day 20
    solver.add(starts[-1] + durations[-1] - 1 == total_days)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_day = 1
        for i in range(n):
            d_val = model.eval(durations[i]).as_long()
            end_day = current_day + d_val - 1
            day_range = f"Day {current_day}-{end_day}"
            itinerary.append({'day_range': day_range, 'place': cities[i]})
            current_day = end_day + 1  # Next city starts immediately after
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()