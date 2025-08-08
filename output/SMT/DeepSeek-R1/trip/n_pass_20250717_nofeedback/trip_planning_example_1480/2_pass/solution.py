from z3 import *

def main():
    # Define the list of cities
    cities = ["Geneva", "Istanbul", "Venice", "Munich", "Reykjavik", "Madrid", "Vienna", "Vilnius", "Brussels"]
    n = len(cities)
    
    # Create the solver
    s = Solver()
    
    # Define the order variables: order[i] is the index of the city at travel position i
    order = [Int(f'order_{i}') for i in range(n)]
    # Each order[i] must be between 0 and n-1
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    # All elements in order must be distinct (permutation)
    s.add(Distinct(order))
    
    # Define start and end days for each travel position
    start_days = [Int(f'start_{i}') for i in range(n)]
    end_days = [Int(f'end_{i}') for i in range(n)]
    
    # Duration constraints for each segment
    for i in range(n):
        duration = end_days[i] - start_days[i] + 1
        s.add(duration >= 2, duration <= 4)
    
    # Itinerary chain constraints
    s.add(start_days[0] == 1)  # Start on day 1
    s.add(end_days[n-1] == 27)  # End on day 27
    for i in range(n-1):
        # No gaps or overlaps: next starts immediately after previous ends
        s.add(end_days[i] + 1 == start_days[i+1])
    
    # Ensure the entire duration sums to 27 days (redundant but added for safety)
    total_days = sum([end_days[i] - start_days[i] + 1 for i in range(n)])
    s.add(total_days == 27)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n):
            # Retrieve the city index for position i
            city_index = model.evaluate(order[i]).as_long()
            city_name = cities[city_index]
            start = model.evaluate(start_days[i]).as_long()
            end = model.evaluate(end_days[i]).as_long()
            # Format the day range
            day_range = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': city_name})
        
        # Output the itinerary
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()