from z3 import *

def main():
    # Define the cities and their durations
    cities = ['Berlin', 'Milan', 'Paris', 'Naples', 'Zurich', 'Lyon', 'Nice', 'Riga', 'Stockholm', 'Seville']
    durations = [1, 2, 4, 3, 4, 2, 1, 2, 2, 2]
    num_cities = len(cities)
    total_days = 23
    
    # Initialize solver
    s = Solver()
    
    # Create a Z3 array for durations
    duration_arr = Array('durations', IntSort(), IntSort())
    for idx, d in enumerate(durations):
        s.add(duration_arr[idx] == d)
    
    # Assignment variables: assign each position in the itinerary to a city index
    assignment = [Int(f'assignment_{i}') for i in range(num_cities)]
    for a in assignment:
        s.add(a >= 0, a < num_cities)
    s.add(Distinct(assignment))
    
    # Start and end day variables for each position
    starts = [Int(f'start_{i}') for i in range(num_cities)]
    ends = [Int(f'end_{i}') for i in range(num_cities)]
    
    # Constraints for each position in the itinerary
    for i in range(num_cities):
        # Duration of the city at position i
        dur_i = duration_arr[assignment[i]]
        # End day = start day + duration - 1
        s.add(ends[i] == starts[i] + dur_i - 1)
        # Days must be within valid range
        s.add(starts[i] >= 1, ends[i] <= total_days)
    
    # Start of the first city must be day 1
    s.add(starts[0] == 1)
    # End of the last city must be day 23
    s.add(ends[num_cities-1] == total_days)
    # Consecutive constraint: end of current city + 1 = start of next city
    for i in range(num_cities - 1):
        s.add(ends[i] + 1 == starts[i+1])
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        for i in range(num_cities):
            city_idx = m.evaluate(assignment[i]).as_long()
            city = cities[city_idx]
            start = m.evaluate(starts[i]).as_long()
            end = m.evaluate(ends[i]).as_long()
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': city})
        
        # Format the plan
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()