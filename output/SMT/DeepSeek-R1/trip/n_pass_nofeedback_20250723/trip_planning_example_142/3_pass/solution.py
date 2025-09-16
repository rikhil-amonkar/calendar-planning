from z3 import *

def main():
    # Define the cities
    cities = ["Madrid", "Dublin", "Tallinn"]
    n_days = 7
    
    # Create Z3 variables for each day
    c = [Int('c_%d' % i) for i in range(n_days)]
    
    s = Solver()
    
    # Each day must be 0, 1, or 2
    for i in range(n_days):
        s.add(And(c[i] >= 0, c[i] <= 2))
    
    # Constraints:
    # Day 1 must be Madrid (0)
    s.add(c[0] == 0)
    # Day 7 must be Tallinn (2)
    s.add(c[6] == 2)
    # Must visit Dublin (1) at least once
    s.add(Or([c[i] == 1 for i in range(n_days)]))
    # Adjacency constraint: consecutive days can only have city indices differing by at most 1
    for i in range(n_days - 1):
        s.add(Abs(c[i] - c[i+1]) <= 1)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Extract the city for each day
        city_list = [model.evaluate(c[i]).as_long() for i in range(n_days)]
        city_names = [cities[idx] for idx in city_list]
        
        # Group consecutive days with the same city
        itinerary = []
        i = 0
        while i < n_days:
            j = i
            current_city = city_names[i]
            while j < n_days and city_names[j] == current_city:
                j += 1
            start_day = i + 1
            end_day = j
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            itinerary.append({'day_range': day_range_str, 'place': current_city})
            i = j
        
        # Output the itinerary
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()